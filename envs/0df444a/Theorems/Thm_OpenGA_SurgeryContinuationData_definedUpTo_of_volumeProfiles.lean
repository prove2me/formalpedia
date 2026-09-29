-- Prove2me | Theorems.Thm_OpenGA_SurgeryContinuationData_definedUpTo_of_volumeProfiles
-- name    : OpenGA.SurgeryContinuationData.definedUpTo_of_volumeProfiles
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T18:33:21.2636+00:00
-- url     : https://prove2.me/theorems/f191f979-2e06-4198-af0f-8c25a7a1e8cf
-- title:
--   All-time existence for a Ricci flow with surgery from volume control
-- statement:
--   Let $C$ be a surgery continuation datum all of whose surgeries occur at positive times, and suppose that for every horizon $T>0$ the flow carries a surgery volume profile on $[0,T]$ whose set of surgery times is exactly the set of surgery times of $C$ lying in $(0,T]$. Then the flow is defined for all time:
--   $$\mathrm{Def}(T)\quad\text{for every } T\ge 0 .$$
--
--   This is the existence assertion of Kleiner–Lott's Section 77 with its two ingredients made explicit. A volume profile on a horizon $[0,T]$ consists of the exponential volume growth estimate along the flow together with the definite volume loss $h^3$ at each surgery of Remark 73.5; it forces the surgery times below $T$ to be finite in number. The continuation datum supplies the prolongation mechanism of Lemma 73.7, coming from the $r$-canonical neighbourhood assumption, and the flow then reaches every finite time.
--
--   The surgery times need not be finite in number globally: only finiteness on each finite horizon is obtained, and only that is needed.
-- source:
--   Kleiner-Lott, Notes on Perelman's papers, https://arxiv.org/abs/math/0605667, Section 77, p. 147, together with Remark 73.5 (p. 140) and Lemma 73.7 (p. 140)

import Definitions.Def_OpenGA_SurgeryContinuationData
import Definitions.Def_OpenGA_SurgeryVolumeProfile

set_option autoImplicit false
open Set

theorem OpenGA.SurgeryContinuationData.definedUpTo_of_volumeProfiles
    (C : OpenGA.SurgeryContinuationData)
    (prof : ∀ T : ℝ, 0 < T → OpenGA.SurgeryVolumeProfile 0 T)
    (hprof : ∀ (T : ℝ) (hT : 0 < T),
      (prof T hT).surgeryTimes = C.surgeryTimes ∩ Ioc 0 T)
    (hpos : ∀ t ∈ C.surgeryTimes, 0 < t) (T : ℝ) (hT : 0 ≤ T) :
    C.DefinedUpTo T := by sorry
