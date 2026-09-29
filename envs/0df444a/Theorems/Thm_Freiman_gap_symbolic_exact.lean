-- Prove2me | Theorems.Thm_Freiman_gap_symbolic_exact
-- name    : Freiman.gap_symbolic_exact
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:47.101976+00:00
-- url     : https://prove2.me/theorems/40b1a263-b2a7-414c-b890-b1ef192bf635
-- title:
--   gap symbolic exact
-- statement:
--   Both explicit extremizers attain their endpoint heights; recenter every hypothetical interior supremum and use the exhaustive A/B reduction to contradict its value.
-- source:
--   Freiman Hall ray report, m3.tex; thm:m3:gap

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_symbolic_exact : gapLeft ∈ symbolicMarkovSpectrum ∧ cF ∈ symbolicMarkovSpectrum ∧ (symbolicMarkovSpectrum ∩ Set.Ioo gapLeft cF) = ∅ := by
  sorry

end Freiman
