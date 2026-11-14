-- Prove2me | Theorems.Thm_NarrowDNF_BourgainEstimate_paper_smallComponentMass_bound
-- name    : NarrowDNF.BourgainEstimate.paper_smallComponentMass_bound
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:53:37.121662+00:00
-- url     : https://prove2.me/theorems/33f6756c-935c-4cfe-8dde-4b78b3525dfe
-- title:
--   Small Fourier-component mass at the paper’s real cutoff
-- statement:
--   Let \(\iota\) be finite, \(0<p<1\), and let \(f:\{0,1\}^{\iota}\to\{0,1\}\). Under independent Bernoulli measure \(\mu_p\), write \(f_S(x)=\widehat f(S)\chi_S(x)\) for its biased Fourier component, with \(\chi_S(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}}\) and \(\widehat f(S)=\mathbb E_p[f\chi_S]\). Suppose real \(k\ge5\), \(0<e\le1\), and integer \(C\ge0\) satisfy \(I_p(f)\le C\le k\); here \(I_p(f)\) sums disagreement probabilities under independent resampling of each coordinate. Set \(\eta=3^{-10k^2}e^{10k}\). Then
--   $$\sum_{|S|\le k}\mathbb E_p\bigl[f_S(x)^2\mathbf1_{|f_S(x)|\le\eta}\bigr]\le e^2/k.$$
--   The cutoff is real and the threshold applies to component values.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainEstimate.lean#L91-L109

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_BourgainComponents
import Definitions.Def_NarrowDNF_BourgainParameters
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_FourierTruncation
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiParameters
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_BourgainEstimate_smallComponentMass_bound

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.BourgainEstimate
end NarrowDNF.BourgainEstimate

namespace NarrowDNF.BourgainRealCutoff
end NarrowDNF.BourgainRealCutoff

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainEstimate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainEstimate.paper_smallComponentMass_bound {p k e : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (C : ℕ) (hk : 5 ≤ k) (he : 0 < e) (he1 : e ≤ 1)
    (hC : (C : ℝ) ≤ k) (hI : Influence.totalInfluence p f ≤ C) :
    FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x)) k
      (HatamiParameters.epsilonOne k e) ≤ e^2/k := by sorry
