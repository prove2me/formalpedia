-- Prove2me | Theorems.Thm_OncePaid_Sparse_eq_4_2
-- name    : OncePaid.Sparse.eq_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:48:54.121383+00:00
-- url     : https://prove2.me/theorems/76af2d4f-5ef4-4504-b894-3ee3b4ba5da9
-- title:
--   §4.1, Eq. (4.2) — $f_T(c,z)=\mathrm{EC}_{H_\ell}(c)+\sum_j z_j$ for all prices; $d=103n$, $L=206n$, $I=1+515n$
-- statement:
--   Let $\ell$ be a prime with $\ell\equiv305\pmod{404}$, $i^2=-1$ in $\mathbb F_\ell$, $n=\ell(\ell^2-1)/2$, and let $w$ be the forced-run source of the LPS host $H_\ell$ for any order of its $2n$ vertices and any order inside each zero-run, with target $T=(01)^{2n}$. For all real edge prices $c$ and marker prices $z=(z_1,\dots,z_n)$ (signed prices allowed),
--
--   $$
--   f_T(c,z)\ =\ \mathrm{EC}_{H_\ell}(c)+\sum_{j=1}^n z_j, \tag{4.2}
--   $$
--
--   where $\mathrm{EC}_{H_\ell}$ is the minimum-weight full edge cover (minimum over all edge sets meeting every vertex). Moreover there are $d=103n$ resources, the source has $L=206n$ positions, the target has length $4n$, and $I=1+d+2L=1+515n$.
--
--   The identity is the exact transfer from bipartite edge cover to once-paid subsequences; it is also the content of the polynomial-time algorithm remarked after Corollary 4.2.
--
--   Differences from the source:
--   - encoding: "the graph's $2n$ vertices in any fixed order" and the order inside each run → parameters $\sigma:\mathrm{Fin}(2n)\simeq V_L\sqcup V_R$ and `runs` with `ValidRuns`, every choice; markers $z_1,\dots,z_n$ → `Fin n`, 0-based; reason: Lean representation of "any fixed order".
--   - encoding: $f_T$ and $\mathrm{EC}_{H_\ell}$ (possibly $+\infty$) → values in `WithTop ℝ`; reason: Lean convention for $\min\emptyset=+\infty$.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 21, §4.1, Eq. (4.2) (PDF p. 23)

import Mathlib
import Definitions.Def_OncePaid_Sparse_OncePaid
import Definitions.Def_OncePaid_Sparse_BipHost
import Definitions.Def_OncePaid_Sparse_ForcedRun
import Definitions.Def_OncePaid_Sparse_LPS

namespace OncePaid.Sparse

/-- §4.1, Eq. (4.2), p. 21. For every prime `ℓ ≡ 305 (mod 404)`, every `i` with `i² = −1`,
`n = ℓ(ℓ² − 1)/2`, every vertex order `σ` of the `2n` vertices of `H_ℓ` and every valid
within-run order, the forced-run source `w` with target `T = (01)^{2n}` satisfies, for all real
edge prices `c` and marker prices `z`, `f_T(c, z) = EC_{H_ℓ}(c) + Σ_j z_j`; moreover there are
`d = 103n` resources, `L = 206n` source positions, the target has length `4n`, and
`I = 1 + d + 2L = 1 + 515n`. -/
theorem eq_4_2 (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ % 404 = 305) (i : ZMod ℓ) (hi : i ^ 2 = -1)
    (σ : Fin (2 * lpsN ℓ) ≃ (lpsLeft ℓ ⊕ lpsRight ℓ))
    (runs : lpsLeft ℓ ⊕ lpsRight ℓ → List (Edge (lpsAdj ℓ i))) (hruns : ValidRuns runs) :
    (∀ (c : Edge (lpsAdj ℓ i) → ℝ) (z : Fin (lpsN ℓ) → ℝ),
      onceOpt (forcedRunSource (lpsN ℓ) σ runs) (alternatingTarget (2 * lpsN ℓ))
          (Sum.elim c z) =
        edgeCoverValue (lpsAdj ℓ i) c + (((∑ j, z j : ℝ)) : WithTop ℝ)) ∧
    Fintype.card (Edge (lpsAdj ℓ i) ⊕ Fin (lpsN ℓ)) = 103 * lpsN ℓ ∧
    (forcedRunSource (lpsN ℓ) σ runs).length = 206 * lpsN ℓ ∧
    (alternatingTarget (2 * lpsN ℓ)).length = 4 * lpsN ℓ ∧
    1 + Fintype.card (Edge (lpsAdj ℓ i) ⊕ Fin (lpsN ℓ)) +
        2 * (forcedRunSource (lpsN ℓ) σ runs).length = 1 + 515 * lpsN ℓ := by sorry

end OncePaid.Sparse
