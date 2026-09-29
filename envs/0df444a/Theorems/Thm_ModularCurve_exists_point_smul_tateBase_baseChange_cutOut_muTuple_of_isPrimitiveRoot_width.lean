-- Prove2me | Theorems.Thm_ModularCurve_exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot_width
-- name    : ModularCurve.exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot_width
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/a3b929be-7859-5907-afa9-0d794e9eb6c0
-- title:
--   Order-M' toric point on a twisted Tate curve of width w
-- statement:
--   Let $F$ be a field, $\Lambda$ a field equipped with an $F(\!(q)\!)$-algebra structure (here $F(\!(q)\!)$ is `LaurentSeries F`), and let $w, M'$ be nonzero natural numbers such that the image of $M'$ in $F$ is nonzero; let $\zeta \in F$ be a primitive $M'$-th root of unity and let $C$ be a Weierstrass variable change over $\Lambda$. Write $E_w$ for [`ModularCurve.tateBase F w`](def/ModularCurve_TateSlots.html#L46), the Tate curve over $F(\!(q)\!)$ obtained from the formal Tate curve `tateLaurent F` by the substitution $q \mapsto q^{w}$, and $E_w^{\Lambda}$ for its base change to $\Lambda$. The assertion is that the affine point group of the twisted curve $C \bullet E_w^{\Lambda}$ contains a point $g$ with the following four properties. First, $n \cdot g = 0$ exactly when $M' \mid n$. Second, for every $n$ with $M' \nmid n$ the transport `vcFun C` of $n\cdot g$ back to $E_w^{\Lambda}$ is the affine point whose coordinates are the images in $\Lambda$ of the two components of [`ModularCurve.toricPoint F w (ζ ^ n)`](def/ModularCurve_TateSlots.html#L125) (the explicit $q^{w}$-expansions $X(\zeta^n), Y(\zeta^n)$), together with a nonsingularity witness for that pair. Third, $g$ has additive order exactly $M'$, and for every prime $p \mid M'$, writing $k = v_p(M')$, every multiple $n\cdot g$ which is an affine point $(x_1,y_1)$ and has order $p^{k}$ satisfies that $x_1$ is a root of the polynomial $$\mathrm{C}(u^{-2d})\cdot h_p\big(\mathrm{C}(u)^2 X + \mathrm{C}(r)\big), \qquad d = \mathtt{gamma0PowDeg}\,p\,k = \begin{cases} 1 & p^{k}=2,\\ \varphi(p^{k})/2 & \text{otherwise},\end{cases}$$ where $u, r$ are the corresponding data of $C$ and $h_p = \prod_{a} \bigl(X - \mathrm{C}(X(\zeta^{a M'/p^{k}}))\bigr)$, the product running over $1 \le a \le p^{k}/2$ with $p \nmid a$, the abscissae again being taken in $\Lambda$ via the structure map. Fourth, conversely, for each prime $p \mid M'$ an element $x_1 \in \Lambda$ is a root of that same transported polynomial if and only if there are $y_1$, a nonsingularity witness, and a point $P$ in the subgroup of multiples of $g$ of order $p^{v_p(M')}$ with $P = (x_1,y_1)$.
--
--   This is the Tate-curve cut-out statement at arbitrary width $w \ge 1$: on the twisted Tate curve of parameter $q^{w}$ over $\Lambda$ the multiples of $g$ are precisely the toric points attached to the powers of $\zeta$, and for each prime power $p^{k}$ exactly dividing $M'$ the points of order $p^{k}$ in $\langle g\rangle$ are cut out by the $C$-transport of the kernel polynomial of $\mu_{p^{k}}$. It supplies the Tate-curve test object used when evaluating level structures and Diamond operators at the cusp, and is applied in the full-level computation [`ModularCurve.FullLevel.Diamond.algebraMap_jqNModC_eq_cyclicQuotientJ_of_eq_map_rigidDataH1Pow_of_tatePoint_pinGamma1`](thm.html#ModularCurve.FullLevel.Diamond.algebraMap_jqNModC_eq_cyclicQuotientJ_of_eq_map_rigidDataH1Pow_of_tatePoint_pinGamma1); the special cases $w = q\ell$ and $w = q$ correspond to full level and to $H_1$ level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot_width.lean

import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot_width
    (F : Type) [Field F] [DecidableEq F] (Λ : Type) [Field Λ] [DecidableEq Λ] [Algebra (LaurentSeries F) Λ]
    (w M' : ℕ) [NeZero w] [NeZero M'] (hM'F : ((M' : ℕ) : F) ≠ 0)
    (ζ : F) (hζ : IsPrimitiveRoot ζ M')
    (C : WeierstrassCurve.VariableChange Λ) :
    ∃ g : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Point,
      (∀ n : ℕ, n • g = 0 ↔ M' ∣ n) ∧
      (∀ n : ℕ, ¬ M' ∣ n →
        ∃ h₁ : ((ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F w (ζ ^ n)).1)
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F w (ζ ^ n)).2),
          WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ) (n • g) =
            WeierstrassCurve.Affine.Point.some _ _ h₁) ∧
      (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Λ)
          (h₁ : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          ((fun p : ↥M'.primeFactors =>
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (Polynomial.X - Polynomial.C (algebraMap (LaurentSeries F) Λ
              (ModularCurve.toricPoint F w ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1)))) p).IsRoot x₁) ∧
      (∀ (p : ↥M'.primeFactors) (x₁ : Λ),
        ((fun p : ↥M'.primeFactors =>
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (Polynomial.X - Polynomial.C (algebraMap (LaurentSeries F) Λ
              (ModularCurve.toricPoint F w ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1)))) p).IsRoot x₁ ↔
          ∃ (P : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Point) (y₁ : Λ)
            (h₁ : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular x₁ y₁),
            P ∈ AddSubgroup.zmultiples g ∧ addOrderOf P = (p : ℕ) ^ M'.factorization (p : ℕ) ∧
            P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := by sorry
