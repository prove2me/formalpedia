-- Prove2me | Theorems.Thm_FourBlockIP350_Main_value_witness_oracle
-- name    : FourBlockIP350.Main.value_witness_oracle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:09.183921+00:00
-- url     : https://prove2.me/theorems/6b95e8cb-6d31-49ac-94e0-5be288a8ee74
-- title:
--   Lemma 3.2 — Value and witness oracle
-- statement:
--   For finite nonempty variable intervals, there is a uniform algorithm computing the exact penalized value and an attaining local vector for every integer $x$, including points outside the global box:
--   $$F(x)=v,\qquad y\text{ attains the inner minimum},\qquad
--   \text{time}\le f(k,\bar\Delta)(1+|I|+\operatorname{enc}(x))^d.$$
--   Here $f$ is one total computable parameter function and $d$ an absolute exponent. The output contains the integer value $v$ and the entire local witness $y$.
--
--   This is a numerical value-and-witness oracle, with its cost measured in binary steps.
--
--   Differences from the source:
--   - encoding: binary time f(k, Δbar)(|I| + enc(x))^{O(1)} → one fixed finite-alphabet multitape machine; one machine-computable f; one natural exponent; f(k, Δbar)(1+|enc(I)|+|enc(x)|)^d; reason: the input includes the entire global vector x; delimited binary encodings preserve the source length bound up to polynomial overhead
--   - encoding: compute F(x) and an attaining local vector y → y is returned and residual slacks are computed uniquely from x,y; reason: F is integer-valued under the standing box assumptions, and the equality determines each residual slack uniquely
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 7, Lemma 3.2

import Mathlib
import Definitions.Def_FourBlockIP350_Main_BinaryEncoding
import Definitions.Def_FourBlockIP350_Main_Penalty

namespace FourBlockIP350.Main

open scoped BigOperators

theorem value_witness_oracle :
    ∃ P : IntMul.MultitapeTM, ∃ f : ℕ → ℕ → ℕ, ComputablePairFunction f ∧
    ∃ d : ℕ, ∀ k n Δ : ℕ, 0 < k → 0 < n → 0 < Δ →
      ∀ I : FourBlock k n, I.localPart.Bounded Δ → GoodBox I →
      ∀ x : ZVec k, ∃ y : LocalCol k n → ℤ, ∃ v : ℤ,
        Attains I x y ∧ F I x = ((v : ℝ) : EReal) ∧
        ComputesWithin P (encFourBlock I ++ encVector (List.finRange k) x)
          (encInt v ++ encVector (localOrder k n) y)
          (f k Δ * (1 + (encFourBlock I).length +
            (encVector (List.finRange k) x).length)^d) := by sorry

end FourBlockIP350.Main
