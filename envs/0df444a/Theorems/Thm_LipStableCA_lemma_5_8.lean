-- Prove2me | Theorems.Thm_LipStableCA_lemma_5_8
-- name    : LipStableCA.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:59.880172+00:00
-- url     : https://prove2.me/theorems/22421fa8-1d55-4183-be14-abbb0b9c691b
-- title:
--   Lemma 5.8 — the Lipschitz constant of Mechanism 3
-- statement:
--   Let $L=\lfloor\log_2m\rfloor$, let $k=2^\ell$ be the random number of blocks of Mechanism 3, let $\tau=\frac12\log 2$, and let
--   $$\phi_m=\mathbb E[k^{-1}]=\frac23+2^{-L-1}-\frac{4^{-L}}6.$$
--   Then
--   $$\mathrm{Lip}(S)\le\frac{15m}{8\tau}\phi_m=\frac{15\,\phi_m}{4\log 2}\,m<6m.$$
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: a total order on $\mathcal F_Q$ in each run → one `LinearOrder` on sets of bidders, for every such order; reason: its restriction to each $\mathcal F_Q$ is the fixed order of that run
--   - encoding: the identity defining $\phi_m$ on p.26 → an extra first clause, $\sum_\ell\Pr[\ell]2^{-\ell}=\phi_m$; reason: it records the printed closed form the bound relies on
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 5.8, p.26

import Definitions.Def_LipStableCA_randomBlock
import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **Lemma 5.8.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.26. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. one `LinearOrder` on sets of bidders, for every such order: its restriction to each `F_Q` is the fixed order of that run. an extra first clause, `Σ_ℓPr[ℓ]2^{-ℓ}=phi_m`: it records the printed closed form the bound relies on. -/
theorem lemma_5_8 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Finset (Fin n))) :
    ∑ l : Fin (blockLevel m + 1), levelProb (blockLevel m) l.val * ((2 : ℝ) ^ l.val)⁻¹ = phiM m ∧
    IsLipschitz ((randomBlock ord : Mechanism n m (BlockSeed n m)).law (blockMeasure n m))
      (15 * (m : ℝ) / (8 * (1 / 2 * Real.log 2)) * phiM m) ∧
    15 * (m : ℝ) / (8 * (1 / 2 * Real.log 2)) * phiM m = 15 * phiM m / (4 * Real.log 2) * (m : ℝ) ∧
    15 * phiM m / (4 * Real.log 2) * (m : ℝ) < 6 * (m : ℝ) := by sorry

end LipStableCA
