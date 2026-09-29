-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/3c2520e2-a6bc-5711-8c29-767250c363f6
-- title:
--   Vanishing on GL₂(𝒪) for level below both conductors
-- statement:
--   Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_v$ for the $v$-adic completion with its valuation $\mathrm{v}$, let $b$ be a natural number, and let $\mu_1, \mu_2 : F^\times \to \mathbb{C}^\times$ be group homomorphisms, each assumed non-trivial somewhere on the set of $u \in F^\times$ with $\mathrm{v}(u) = 1$ and, when $b \neq 0$, $\mathrm{v}(u - 1) \le \exp(-b)$. Let $F_0 : GL_2(F) \to \mathbb{C}$ satisfy: (i) $F_0(\mathrm{diag}(u_1,u_2)\,k) = \mu_1(u_1)\mu_2(u_2) F_0(k)$ whenever $\mathrm{v}(u_1) = \mathrm{v}(u_2) = 1$ and all entries of $k$ and of $k^{-1}$ have valuation $\le 1$; (ii) $F_0\big(\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)k\big) = F_0(k)$ for such $k$ and $\mathrm{v}(x) \le 1$; (iii) $F_0(k\,\mathrm{diag}(u,1)) = F_0(k)$ for every $k \in GL_2(F)$ and every $u$ with $\mathrm{v}(u) = 1$; (iv) $F_0\big(k\left(\begin{smallmatrix}1&s\\0&1\end{smallmatrix}\right)\big) = F_0(k)$ and $F_0\big(k\left(\begin{smallmatrix}1&0\\s&1\end{smallmatrix}\right)\big) = F_0(k)$ for every $k \in GL_2(F)$ and every $s$ with $\mathrm{v}(s) \le \exp(-b)$. Then $F_0(k) = 0$ for every $k$ all of whose entries and whose inverse's entries have valuation $\le 1$.
--
--   This is the elementary half of Casselman's conductor formula $a(I(\mu_1,\mu_2)) = a(\mu_1) + a(\mu_2)$: a vector in a principal series with both inducing characters of conductor exceeding $b$, invariant under $\mathrm{diag}(\mathcal{O}^\times,1)$ and under the upper and lower unipotents of level $b$, must vanish on the integral points of $GL_2(F)$, hence vanish identically by Iwasawa decomposition. It is used in the cubic induction step to force vanishing of principal-series vectors at level $b$ and thereby to kill the Weyl-element sums occurring there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level
    (v : HeightOneSpectrum (𝓞 ℚ)) (b : ℕ) (μ₁ μ₂ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hμ₁ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, μ₁ u ≠ 1)
    (hμ₂ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, μ₂ u ≠ 1)
    (F₀ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hleft : ∀ (u₁ u₂ : (v.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (v.adicCompletion ℚ)),
      (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      Valued.v (u₁ : v.adicCompletion ℚ) = 1 → Valued.v (u₂ : v.adicCompletion ℚ) = 1 →
      F₀ (LanglandsTunnell.CubicInduction.diagUnits2 u₁ u₂ * k) =
        ((μ₁ u₁ : ℂˣ) : ℂ) * ((μ₂ u₂ : ℂˣ) : ℂ) * F₀ k)
    (hleftU : ∀ (x : v.adicCompletion ℚ) (k : GL (Fin 2) (v.adicCompletion ℚ)),
      (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      Valued.v x ≤ 1 →
      F₀ (AutomorphicForm.unipotentGL2 x * k) = F₀ k)
    (hdiag : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 → F₀ (k * LanglandsTunnell.CubicInduction.diagUnitGL2 u) = F₀ k)
    (hupper : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) → F₀ (k * AutomorphicForm.unipotentGL2 s) = F₀ k)
    (hlower : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      F₀ (k * Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0; s, 1]
        (by simp [Matrix.det_fin_two_of])) = F₀ k)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    F₀ k = 0 := by sorry
