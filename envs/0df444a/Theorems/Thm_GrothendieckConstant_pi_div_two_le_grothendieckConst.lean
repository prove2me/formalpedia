-- Prove2me | Theorems.Thm_GrothendieckConstant_pi_div_two_le_grothendieckConst
-- name    : GrothendieckConstant.pi_div_two_le_grothendieckConst
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T18:29:23.256443+00:00
-- url     : https://prove2.me/theorems/dd80d9eb-6a63-437a-8aa8-5676503f4783
-- title:
--   $K_G\ge\pi/2$
-- statement:
--   Grothendieck's original work already yields the lower bound
--
--   $$K_G\ \ge\ \frac{\pi}{2}=1.5707\ldots$$
--
--   for the Grothendieck constant $K_G$, the least $K$ with $\mathrm{SDP}(A)\le K\cdot\mathrm{OPT}(A)$ for all real matrices $A$. It is the classical entry point to the lower-bound side of the problem and the benchmark that the Davie-Reeds hard instance later improved to $1.6769\ldots$
-- source:
--   Li, Saha, Xue, Chaudhuri, Klivans, Kothari, Meka, "Long-Horizon AI Research for Grothendieck Constant: A Case Study in Human-AI Mathematical Collaboration", arXiv:2608.11195v3 (2026), https://arxiv.org/abs/2608.11195, Section 2, p. 6 ("Grothendieck's own work implies K_G >= pi/2 ...")

import Mathlib
import Definitions.Def_GrothendieckConstantDefs

namespace GrothendieckConstant

theorem pi_div_two_le_grothendieckConst : Real.pi / 2 ≤ grothendieckConst := by sorry

end GrothendieckConstant
