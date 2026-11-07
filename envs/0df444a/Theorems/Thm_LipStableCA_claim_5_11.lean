-- Prove2me | Theorems.Thm_LipStableCA_claim_5_11
-- name    : LipStableCA.claim_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:00.428754+00:00
-- url     : https://prove2.me/theorems/3b03ee8d-e55b-440b-bf8d-ed85f46988d8
-- title:
--   Claim 5.11 — many blocks have large value
-- statement:
--   Let $S^*$ be an optimal allocation for the profile $v$. For $t>0$, let $H_t=\{i\in N:v_i(S^*_i)\ge t\}$, and let $Y_t$ be the number of $b\in[k]$ with $V_b\ge t$ in Mechanism 3. Then
--   $$\mathbb E[Y_t]\ge\frac{\log(m+1)}{8m}\,|H_t|.$$
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: the expectation $\mathbb E[Y_t]$ → integrability of $Y_t$ as an extra conclusion; reason: $Y_t$ is bounded and depends only on discrete choices
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 5.11, p.27

import Definitions.Def_LipStableCA_randomBlock
open MeasureTheory
open ComplementFreeCA.CFRounding
open Classical

namespace LipStableCA

/-- **Claim 5.11.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.27. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. integrability of `Y_t` as an extra conclusion: `Y_t` is bounded and depends only on discrete choices. -/
theorem claim_5_11 {n m : ℕ} (hm : 1 ≤ m) (v : Profile n m) (hv : IsProfile v) (Sstar : Alloc n m)
    (hS : welfare v Sstar.1 = opt v) (t : ℝ) (ht : 0 < t) :
    Integrable (fun ω => (blockCountAbove v ω t : ℝ)) (blockMeasure n m) ∧
      Real.log ((m : ℝ) + 1) / (8 * (m : ℝ)) *
          ((Finset.univ.filter fun i => t ≤ v i (Sstar.1 i)).card : ℝ) ≤
        ∫ ω, (blockCountAbove v ω t : ℝ) ∂(blockMeasure n m) := by sorry

end LipStableCA
