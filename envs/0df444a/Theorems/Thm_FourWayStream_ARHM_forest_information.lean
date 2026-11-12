-- Prove2me | Theorems.Thm_FourWayStream_ARHM_forest_information
-- name    : FourWayStream.ARHM.forest_information
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:24.521318+00:00
-- url     : https://prove2.me/theorems/4aca1c7c-a27c-4a89-b119-d6cce7f1bf01
-- title:
--   Lemma 6.5 — forest information with side information
-- statement:
--   **Lemma 6.5 (Forest information with side information).** Let $N\ge2$ be even, $m\ge1$, $X$ uniform on $\{0,1\}^N$, and let Bob's requests $M=(M_1,\dots,M_m)$ be drawn independently from a distribution $D$ on perfect matchings, independently of $X$. Consider an instance of $\mathrm{MHM}_{N,m}$ and an arbitrary one-way protocol whose message has $q$ qubits. Let $O$ be Bob's classical output, $\Lambda$ any random variable on the same probability space, and $E_\Lambda\subseteq\{e_1,\dots,e_m\}$ a set of output edges such that $E_\Lambda$ and the true parities $X_u\oplus X_v$ of its edges are determined by $(O,M,\Lambda)$. Then
--   $$q\ge I(X:O\mid M)\ge E[\mathrm{fs}(E_\Lambda)]-H(\Lambda\mid O,M).$$
--
--   Correct parities on the edges of a forest are independent constraints on $X$; this lemma turns a large forest of correctly answered edges into a lower bound on the message length.
--
--   **Formalization Note** $\Lambda$ is given by its conditional law given the coins, $X$, $M$ and $O$; this covers every random variable on the probability space, since only the joint law of $(X,M,O,\Lambda)$ enters the statement. $E_\Lambda$ is the set of edges of the output rounds selected by a function of $(O,M,\Lambda)$, and "determined" is required on the support of the joint law.
--
--   Differences from the source:
--   - generalization: Bob receives perfect matchings M_t drawn from D → Bob receives requests q_t from a finite set Q, drawn from D and naming the matchings μ(q_t); reason: Q = perfect matchings and μ = id is the source's setting
--   - encoding: Bob's decoding operation on the message → a POVM on the message depending on the coins and all requests; reason: any operation of Bob with a classical output, with ancillas independent of X, induces such a POVM
--   - encoding: a message of q qubits → a density matrix on C^d with d ≤ 2^q; reason: §4.3: a state of dimension at most 2^q
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §6.2, p.29, Lemma 6.5 (standing assumptions of §6.2, p.28; budget (1), p.29)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Lemma 6.5 (Forest information with side information), p.29. Consider `MHM_{N,m}` (`N ≥ 2`
even, `m ≥ 1`, `X` uniform, requests i.i.d. from a distribution `D` on perfect matchings) and an
arbitrary one-way protocol whose message has `q` qubits. Let `O` be Bob's output, `Λ` any random
variable on the same probability space (given by its conditional law `κ`), and `E_Λ` a set of output
edges (those of the rounds `sel(O, M, Λ)`) such that `E_Λ` and the true parities `X_u ⊕ X_v` of its
edges are determined by `(O, M, Λ)`. Then `q ≥ I(X : O | M) ≥ E[fs(E_Λ)] − H(Λ | O, M)`. -/
theorem forest_information (N m : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m)
    {Q : Type} [Fintype Q] [DecidableEq Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ)
    (hD : IsMatchingDist μ D) {nR : ℕ} (P : SimProtocol N m Q nR) (hP : P.Valid)
    (q : ℕ) (hq : P.d ≤ 2 ^ q) {nΛ : ℕ}
    (κ : Fin nR → (Fin N → Bool) → (Fin m → Q) → (Fin m → Output N) → Fin nΛ → ℝ)
    (hκ : ∀ r x qs o, (∀ l, 0 ≤ κ r x qs o l) ∧ ∑ l, κ r x qs o l = 1)
    (sel : (Fin m → Output N) → (Fin m → Q) → Fin nΛ → Finset (Fin m))
    (par : (Fin m → Output N) → (Fin m → Q) → Fin nΛ → Fin m → Bool)
    (hpar : ∀ ω : SimProtocol.SideSample N m Q nR nΛ, P.sideLaw D κ ω ≠ 0 →
      ∀ t ∈ sel ω.2.2.2.1 ω.2.2.1 ω.2.2.2.2, ∀ e b, ω.2.2.2.1 t = some (e, b) →
        edgeParity ω.2.1 e = par ω.2.2.2.1 ω.2.2.1 ω.2.2.2.2 t) :
    condMutualInfoOf (P.sideLaw D κ) (fun ω => ω.2.1) (fun ω => ω.2.2.2.1) (fun ω => ω.2.2.1)
        ≤ q ∧
    expect (P.sideLaw D κ)
        (fun ω => (forestSize (selEdges ω.2.2.2.1 (sel ω.2.2.2.1 ω.2.2.1 ω.2.2.2.2)) : ℝ)) -
        condEntropyOf (P.sideLaw D κ) (fun ω => ω.2.2.2.2) (fun ω => (ω.2.2.2.1, ω.2.2.1)) ≤
      condMutualInfoOf (P.sideLaw D κ) (fun ω => ω.2.1) (fun ω => ω.2.2.2.1)
        (fun ω => ω.2.2.1) := by sorry

end FourWayStream.ARHM
