-- Prove2me | Theorems.Thm_LipStableCA_lemma_5_9
-- name    : LipStableCA.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:52.977722+00:00
-- url     : https://prove2.me/theorems/24def85e-cb0b-4297-aa51-0f490eebc666
-- title:
--   Lemma 5.9 — the welfare guarantee of Mechanism 3
-- statement:
--   For every profile $v\in\mathcal V^n$, Mechanism 3 satisfies
--   $$\mathrm{SW}(v)\ge\frac{\log(m+1)}{16m}\,\mathrm{OPT}(v).$$
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 5.9, p.27

import Definitions.Def_LipStableCA_randomBlock
import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **Lemma 5.9.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.27. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. -/
theorem lemma_5_9 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Finset (Fin n))) (v : Profile n m)
    (hv : IsProfile v) :
    Real.log ((m : ℝ) + 1) / (16 * (m : ℝ)) * opt v ≤
      expectedWelfare v ((randomBlock ord : Mechanism n m (BlockSeed n m)).law (blockMeasure n m) v) := by sorry

end LipStableCA
