-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_linear_mhm_lower_bound
-- name    : FourWayStream.ARHM.Supplement.linear_mhm_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:05:42.163102+00:00
-- url     : https://prove2.me/theorems/69aeaf63-5872-4ad7-9e10-afcc9df3a4a2
-- title:
--   Theorem 6.7 — linear Multiple Hidden Matching lower bound $\Omega_{\delta,\varepsilon}(m)$ for $m\le N^{1/2-\delta}$
-- statement:
--   Fix $\delta\in(0,1/2)$ and $\varepsilon\in(0,1/2)$. There is a constant $c=c(\delta,\varepsilon)>0$ such that the following holds for every even $N\ge2$, every integer $1\le m\le N^{1/2-\delta}$ and every balanced distribution $D$ on perfect matchings of $[N]$. Let a one-way protocol for $\mathrm{MHM}_{N,m}$ (public coins allowed, Bob receives the whole list and may decode jointly) send a $q$-qubit message. If it answers all $m$ requests correctly with probability at least $1-\varepsilon$ when $X$ is uniform and $M_1,\dots,M_m$ are independent draws from $D$, then
--   $$q\ge c\,m.$$
--   In particular the same holds for every protocol with worst-case joint error at most $\varepsilon$.
--
--   This proves the conjecture of Gilboa, Jain and McClean for $m\le N^{1/2-\delta}$: the message must grow linearly with the number of simultaneous requests.
--
--   **Formalization Note** The paper writes $\Omega_{\delta,\varepsilon}(m)$; $c$ is quantified after $\delta,\varepsilon$ and before $N$, $m$, $D$ and the protocol. The proof on p.45 gives $c=\min\{c_\delta(1-\varepsilon)/4,\,1/m_1\}$ with $c_\delta=\delta/16$, $m_0=4/(c_\delta(1-\varepsilon))$, $N_0=(2/(1-\varepsilon))^{1/\delta}$ and $m_1=\max\{m_0,\sqrt{N_0}\}$.
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: Ω_{δ,ε}(m) qubits → ∃ c > 0 depending only on δ, ε with c·m ≤ q for all N, m, D and protocols in range; reason: the standard meaning of Ω/O with the constant and threshold quantified before every varying parameter, as §4 uses them
--   - encoding: a distribution D on perfect matchings of [N] → a distribution on a finite request type Q, request q naming the perfect matching μ(q); reason: with Q the perfect matchings and μ = id this is the paper’s D; the published base model
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.30, Theorem 6.7 (proof Appendix B, pp.43–45; constants p.45)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols
import Definitions.Def_FourWayStream_ARHM_Supplement_Simultaneous

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem 6.7 (Linear Multiple Hidden Matching lower bound), p.30 (proof pp.43–45). Fix
`δ, ε ∈ (0, 1/2)`. There is `c > 0`, depending only on `δ` and `ε`, such that for every even
`N ≥ 2`, every `1 ≤ m ≤ N^{1/2 − δ}` and every balanced distribution `D` on perfect matchings of
`[N]`, every one-way protocol for `MHM_{N,m}` (Bob receives the whole list and decodes jointly) with
message dimension at most `2^q` that answers all `m` requests correctly with probability at least
`1 − ε`, when `X` is uniform and `M_1, …, M_m` are independent draws from `D`, has `q ≥ c m`; in
particular so does every protocol with worst-case joint error at most `ε`. -/
theorem linear_mhm_lower_bound (δ ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (hε0 : 0 < ε)
    (hε1 : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ N m : ℕ, Even N → 2 ≤ N → 1 ≤ m → (m : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) →
      ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ),
        IsBalanced μ D → ∀ {nR : ℕ} (P : SimProtocol N m Q nR), P.Valid →
        ∀ q : ℕ, P.d ≤ 2 ^ q →
          (1 - ε ≤ jointSucc P μ D → c * m ≤ q) ∧ (WorstCaseJointSucc P μ ε → c * m ≤ q) := by sorry

end FourWayStream.ARHM.Supplement
