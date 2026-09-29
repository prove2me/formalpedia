-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat
-- name    : NumberField.AdelicFourier.exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/666f3153-f4c1-53c6-94e1-8f1290a2ef13
-- title:
--   Gaussian times indicator as a Schwartz–Bruhat function on A_ℚ²
-- statement:
--   Let $S$ be a finite set of primes of $\mathcal{O}_{\mathbb{Q}}$ (points of the height-one spectrum) and let $m$ assign a natural number $m_p$ to every such prime. Then there is a function $\Phi$ on $\mathbb{A}_{\mathbb{Q}}^2$ (functions $\mathrm{Fin}\,2 \to$ the adele ring) with values in $\mathbb{C}$ lying in `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of the pure tensors $x \mapsto g(x_\infty)\,h(x_{\mathrm{fin}})$ with $g$ a Schwartz function on the pair of mixed-space components and $h$ a locally constant, compactly supported function of the pair of finite-adelic components, such that for every $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ the value of $\Phi$ on the second row of $g$, i.e. on `bottomRowVec ℚ g 1` $= (j \mapsto 1 \cdot g_{1j})$, is the product of two factors. The first is $\exp\bigl(-\pi(a_{10}^2 + a_{11}^2)\bigr)$, viewed in $\mathbb{C}$, where $a =$ `ratArchGL2 g` $\in \mathrm{GL}_2(\mathbb{R})$ is obtained from $g$ by passing to its infinite-adelic part, taking the component at the unique (real) infinite place of $\mathbb{Q}$ and identifying that completion with $\mathbb{R}$. The second is $1$ if, writing $g_{1j}$ for the entries of the second row and $(\cdot)_{\mathrm{fin},p}$ for the component at $p$ of the finite part, one has $v_p((g_{1j})_{\mathrm{fin},p}) \le 1$ for all $j$ and all $p \notin S$, and $v_p((g_{10})_{\mathrm{fin},p}) \le \exp(-m_p)$ together with $v_p((g_{11})_{\mathrm{fin},p} - 1) \le \exp(-m_p)$ for all $p \in S$; otherwise it is $0$.
--
--   This produces the test function entering the Godement section attached to the bottom row of a matrix in $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$: the standard Gaussian at the real place, the indicator of $\mathbb{Z}_p^2$ outside $S$, and the indicator of the coset $(0,1) + p^{m_p}\mathbb{Z}_p^2$ at $p \in S$. It is used in the construction of Rankin–Selberg test data over $\mathbb{Q}$, by [`AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat`](thm.html#AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicFourier IsDedekindDomain AutomorphicForm LanglandsTunnell
open scoped Classical

theorem NumberField.AdelicFourier.exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (m : HeightOneSpectrum (𝓞 ℚ) → ℕ) :
    ∃ Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Φ ∈ schwartzBruhat2 ℚ ∧
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Φ (bottomRowVec ℚ g 1) =
          (Real.exp (-(Real.pi *
              (((ratArchGL2 g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((ratArchGL2 g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2))) : ℂ) *
          (if (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
              (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤ WithZero.exp (-(m p : ℤ)) ∧
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤ WithZero.exp (-(m p : ℤ)))
            then (1 : ℂ) else 0) := by sorry
