-- Prove2me | Theorems.Thm_NarrowDNF_narrowDNF_of_hatami
-- name    : NarrowDNF.narrowDNF_of_hatami
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:35:20.06092+00:00
-- url     : https://prove2.me/theorems/e6a2fee3-ddd2-412e-9c2c-80d01cb799d4
-- title:
--   The Hatami arity-and-load theorem implies the low-bias narrow-DNF theorem
-- statement:
--   Assume the following structural assertion. For each $n$, $0<p\le1/2$, Boolean $f$, and $0<a\le1$, put $c=\lceil I_p(f)\rceil$, where $I_p(f)$ is total resampling influence. There are an increasing activation family $J$ and a $J$-measurable Boolean $h$ with error at most $a$, activation arity at most $\lceil1000c/a\rceil$, and load at most $\exp(10^{10}c^2/a^2)$. Then, for every $n\ge1$, $K>0$, $0<p\le1/2$, $0<\varepsilon<1$, and monotone $f$ with $I_p(f)\le K$, there is a positive DNF $g$ such that
--   $$
--   \Pr_p(f\ne g)\le\varepsilon,\qquad
--   \operatorname{width}(g)\le\exp\left(10^{13}(K+1)^2/\varepsilon^2\right).
--   $$
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/MainReduction.lean#L10-L49

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CertificateBounds
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_MainStatements
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_ShiftProbability
import Definitions.Def_NarrowDNF_WidthBound
import Theorems.Thm_NarrowDNF_WidthBound_width_le_exponential
import Theorems.Thm_NarrowDNF_adaptive_approximation_to_dnf

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.ShiftProbability
end NarrowDNF.ShiftProbability

namespace NarrowDNF.WidthBound
end NarrowDNF.WidthBound
noncomputable section
open NarrowDNF

theorem NarrowDNF.narrowDNF_of_hatami (hHatami : HatamiArityLoad) : NarrowDNFApproximation := by sorry
