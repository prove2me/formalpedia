-- Prove2me | Theorems.Thm_NarrowDNF_main_narrow_dnf
-- name    : NarrowDNF.main_narrow_dnf
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T09:07:06.295198+00:00
-- url     : https://prove2.me/theorems/05c31a44-7765-4040-93b0-4390357d7c17
-- title:
--   Theorem 1.2: uniform narrow monotone DNF approximation at low bias
-- statement:
--   There exists an absolute constant $C>0$, independent of every subsequent parameter, such that for every $n\ge1$, $K>0$, $0<p\le1/2$, and $0<\varepsilon<1$, every monotone Boolean function $f$ on $\{0,1\}^n$ with total resampling influence $I_p(f)\le K$ has a positive DNF $g$ satisfying
--   $$
--   \Pr_p(f\ne g)\le\varepsilon,\qquad
--   \operatorname{width}(g)\le\exp\left(C\frac{(K+1)^2}{\varepsilon^2}\right).
--   $$
--   Here $I_p(f)=\sum_i\Pr[f(X)\ne f(X^{i\leftarrow B})]$, where $X$ is product Bernoulli $p$ and $B$ an independent Bernoulli $p$ bit. The construction admits $C=10^{13}$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Paper.lean#L19-L21

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Mathlib.Data.Fintype.Powerset
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
import Definitions.Def_NarrowDNF_MainStatements
import Theorems.Thm_NarrowDNF_HatamiInput_hatami_arity_load
import Theorems.Thm_NarrowDNF_narrowDNF_of_hatami

namespace NarrowDNF
end NarrowDNF
open NarrowDNF

theorem NarrowDNF.main_narrow_dnf : NarrowDNFApproximation := by sorry
