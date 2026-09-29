-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2
-- name    : LanglandsTunnell.CubicInduction.exists_linearMap_stabilised_jacquetIntegral_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/17a41252-a8ec-565c-8810-b600867d73e9
-- title:
--   Stabilised Jacquet functional on the GL₂(ℚₚ) principal series
-- statement:
--   Let $p$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, write $F$ for the completion $\mathbb{Q}_p$ at $p$, and let $\chi = (\chi_0,\chi_1)$ be a pair of monoid homomorphisms $F^\times \to \mathbb{C}^\times$ together with depths $c_0,c_1 \in \mathbb{N}$ such that $\chi_i$ is trivial on `higherUnitsAt ℚ p (cχ i)`, i.e. on the set of units $u$ with $\mathrm{v}(u)=1$ and, unless $c_i=0$, $\mathrm{v}(u-1) \le \exp(-c_i)$. Let $w_0 \in \mathrm{GL}_2(F)$ have underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and let $\theta$ be an additive character of $F$ with values in $\mathbb{C}$ which is trivial on some ball $\{\mathrm{v}(y) \le \exp k\}$, $k \in \mathbb{Z}$, and is not the trivial character. Equip $F$ with its Borel $\sigma$-algebra. The assertion is that for every additive Haar measure $\nu$ on $F$ there exists a $\mathbb{C}$-linear map $\Lambda$ from the space `principalSeries2 p χ` — the submodule of functions $f : \mathrm{GL}_2(F) \to \mathbb{C}$ that are locally constant, satisfy $f\!\left(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\right) = f(g)$ for all $x \in F$, and satisfy $f(\mathrm{diag}(a_0,a_1)g) = \chi_0(a_0)\chi_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,f(g)$ for all units $a_0,a_1$ — to the space of all functions $\mathrm{GL}_2(F) \to \mathbb{C}$, with five properties. First, for each $f$ in the principal series and each $g \in \mathrm{GL}_2(F)$ there is $M_0 \in \mathbb{Z}$ such that for every $M \ge M_0$ the function $y \mapsto f(w_0\, n(y)\, g)\,\theta(y)$, where $n(y) = \begin{pmatrix}1&y\\0&1\end{pmatrix}$, is integrable on $\{\mathrm{v}(y) \le \exp M\}$ with respect to $\nu$ and $\Lambda f\,(g)$ equals its integral over that ball. Secondly, whenever $y \mapsto f(w_0 n(y) g)\theta(y)$ is $\nu$-integrable on all of $F$, $\Lambda f\,(g)$ equals the integral over $F$. Thirdly, $\Lambda f\,(n(x)g) = \theta(x)^{-1}\,\Lambda f\,(g)$ for all $x \in F$ and $g$. Fourthly, $\Lambda$ intertwines the right-translation action $(\,f \mapsto (g \mapsto f(gh))\,)$ on the principal series with right translation of the argument: $\Lambda(\rho(h)f)(g) = \Lambda f\,(gh)$. Finally, there is some $f$ in the principal series with $\Lambda f\,(1) \ne 0$.
--
--   This is the local Whittaker (Jacquet) functional for the normalised principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$, constructed for an arbitrary pair of characters by stabilising the truncated Jacquet integrals rather than by assuming absolute convergence, and agreeing with the honest Jacquet integral whenever the latter converges. It feeds the analysis of flat sections and the construction of Whittaker models for the principal series used in the local theory behind the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_linearMap_stabilised_jacquetIntegral_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (hθk : ∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → θ y = 1)
    (hθ1 : θ ≠ 1) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      ∃ Λ : ↥(principalSeries2 p χ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),

        (∀ (f : ↥(principalSeries2 p χ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), ∃ M₀ : ℤ, ∀ M : ℤ, M₀ ≤ M →
            IntegrableOn (fun y : p.adicCompletion ℚ =>
                (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (w₀ * unipotentGL2 y * g) * θ y)
              {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M} ν ∧
            Λ f g = ∫ y in {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M},
              (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (w₀ * unipotentGL2 y * g) * θ y ∂ν) ∧

        (∀ (f : ↥(principalSeries2 p χ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
            Integrable (fun y : p.adicCompletion ℚ =>
                (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (w₀ * unipotentGL2 y * g) * θ y) ν →
            Λ f g = ∫ y, (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (w₀ * unipotentGL2 y * g) * θ y ∂ν) ∧

        (∀ (f : ↥(principalSeries2 p χ)) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
            Λ f (unipotentGL2 x * g) = (θ x)⁻¹ * Λ f g) ∧

        (∀ (f : ↥(principalSeries2 p χ)) (h g : GL (Fin 2) (p.adicCompletion ℚ)),
            Λ (principalSeries2Rep χ h f) g = Λ f (g * h)) ∧

        (∃ f : ↥(principalSeries2 p χ), Λ f 1 ≠ 0) := by sorry
