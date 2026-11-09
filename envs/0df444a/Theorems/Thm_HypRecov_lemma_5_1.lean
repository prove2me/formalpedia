-- Prove2me | Theorems.Thm_HypRecov_lemma_5_1
-- name    : HypRecov.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:38:25.404315+00:00
-- url     : https://prove2.me/theorems/ed565912-e143-44ca-89d1-d27891544335
-- title:
--   Lemma 5.1 — membership information across a small cut
-- statement:
--   Throughout, $H$ is a simple $r$-uniform hypergraph on $V=\{0,\dots,n-1\}$ with $r\ge 2$, $k\ge 3$, $K=k-1$ and $M=2^{\lceil\log_2 k\rceil-1}$ (so $M\le K<2M$); $D\subseteq E(H)$ is a set of recovered edges and $J=H-D$ the residual hypergraph; $P_0$ is a safe base partition. A **small cut** is a set $S$ with $\mathrm{cut}_H(S)<k$.
--
--   Fix a small cut $S$, put $F=\delta_J(S)$, $t=|F|$, $d_F(v)=|\{e\in F:v\in e\}|$ and $Z=\{v:d_F(v)\ge M\}$. Then:
--
--   1. $t\le K$, and $|Z|\le rt/M<2r$;
--   2. $Z$ is a clique of the two-section $G(J)$;
--   3. if $e\in F$ contains a vertex $x\notin Z$ on a shore $A$ ($A=S$ or $A=V\setminus S$), then $e$ appears in an available complete list, $x\in P_e$, $P_e$ meets both shores, and $U_e\setminus e\subseteq Z\cap A$;
--   4. if $e\in F$ has vertices outside $Z$ on both shores, then $U_e=e$.
--
--   The lemma confines the uncertainty about a boundary edge to one shore of the small clique $Z$.
--
--   Differences from the source:
--   - reading: cache records, edge labels and available complete lists (Proposition 4.1) → the true residual quantities avail, knownMembers, envelope, numPoints; reason: the arguments are deterministic on the cache success event (p.9), where every value read is the true one and labels are injective on T_K (paper.md decision 7)
--   - encoding: P₀ and its current coarsening P safe → P₀ safe; reason: P does not occur in the statement; P safe and coarsening P₀ imply P₀ safe, and P = P₀ is a safe coarsening
--   - reading: U_e, which "additional sound negative certificates may further shrink" → the envelope without extra certificates; reason: it is the largest envelope; the conclusions for it imply those for every sound shrinking containing e
--   - encoding: |Z| ≤ rt/M < 2r; a shore A → real inequalities; A = S ∨ A = Sᶜ; reason: Lean convention
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 5.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_twoSection
import Definitions.Def_HypRecov_Safe
import Definitions.Def_HypRecov_envelope
import Definitions.Def_HypRecov_heavyCore

namespace HypRecov

/-- **Lemma 5.1 (Membership information across a small cut).** Zhang, Chen, Shen, *Hypergraph Recovery
from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 5.1,
p.10 (PDF p.11): "Fix an original small cut S and put F = δ_J(S), t = |F| ≤ K,
d_F(v) = |{e ∈ F : v ∈ e}|, Z = {v : d_F(v) ≥ M}. Then |Z| ≤ rt/M < 2r, and Z is a clique of the true
two-section. If an edge e ∈ F contains a vertex x ∉ Z on a shore A, then its label occurs in an
available complete list, x ∈ P_e, the known-member set P_e meets both shores, and U_e ∖ e ⊆ Z ∩ A. If
e has vertices outside Z on both shores, then U_e = e."

Setting (§4, p.8; §5.1, p.9): `H` simple `r`-uniform, `2 ≤ r`, `k ≥ 3`, `K = k − 1`,
`M = 2^{⌈log₂ k⌉−1}`; `D ⊆ E(H)` recovered edges, `J = H − D`; `P₀` a safe base partition.

**Formalization Note.** Stated on the true residual hypergraph (the cache's success event, paper.md
decision 7): available lists, `P_e`, `U_e` and `Z` are `avail`, `knownMembers`, `envelope` and
`heavyCore`. The current partition `P` does not occur; its safety and coarsening only give that `P₀`
is safe. A shore is `S` or its complement. -/
theorem lemma_5_1 {n : ℕ} (E D : Finset (Finset (Fin n))) (r k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k)
    (hE : ∀ e ∈ E, e.card = r) (hD : D ⊆ E) (P₀ : Fin n → Fin n) (hP₀ : Safe E k P₀)
    (S : Finset (Fin n)) (hS : cut E S < k) :
    (bdry (E \ D) S).card ≤ k - 1 ∧
    ((heavyCore (E \ D) S (Mpow k)).card : ℝ) ≤ (r : ℝ) * (bdry (E \ D) S).card / Mpow k ∧
    (r : ℝ) * (bdry (E \ D) S).card / Mpow k < 2 * r ∧
    (twoSection (E \ D)).IsClique (heavyCore (E \ D) S (Mpow k) : Set (Fin n)) ∧
    (∀ e ∈ bdry (E \ D) S, ∀ A : Finset (Fin n), (A = S ∨ A = Sᶜ) →
      ∀ x ∈ e, x ∉ heavyCore (E \ D) S (Mpow k) → x ∈ A →
        (∃ u ∈ e, ∃ v ∈ e, avail (E \ D) P₀ (Mpow k) u v) ∧
        x ∈ knownMembers (E \ D) P₀ (Mpow k) e ∧
        (knownMembers (E \ D) P₀ (Mpow k) e ∩ S).Nonempty ∧
        (knownMembers (E \ D) P₀ (Mpow k) e \ S).Nonempty ∧
        envelope (E \ D) P₀ (Mpow k) e \ e ⊆ heavyCore (E \ D) S (Mpow k) ∩ A) ∧
    (∀ e ∈ bdry (E \ D) S,
      (∃ x ∈ e, x ∈ S ∧ x ∉ heavyCore (E \ D) S (Mpow k)) →
      (∃ x ∈ e, x ∉ S ∧ x ∉ heavyCore (E \ D) S (Mpow k)) →
      envelope (E \ D) P₀ (Mpow k) e = e) := by sorry

end HypRecov
