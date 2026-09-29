-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
-- name    : LanglandsTunnell.CubicInduction.exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/6651f377-920d-59aa-b111-31e77771f164
-- title:
--   Truncated Jacquet integrals of a flat section: Laurent polynomial in q^u
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and write $F = \mathbb{Q}_p$ for the completion $p.\mathrm{adicCompletion}\ \mathbb{Q}$ and $q =$ `Ideal.absNorm p.asIdeal`. Let $\chi_0,\chi_1 : F^\times \to \mathbb{C}^\times$ be monoid homomorphisms (a family $\chi$ indexed by `Fin 2`), let $c_{\chi} : \mathrm{Fin}\ 2 \to \mathbb{N}$, and assume each $\chi_i$ is trivial on `higherUnitsAt ℚ p (cχ i)`, i.e. on all units $u$ with $v(u)=1$ and, unless $c_\chi(i)=0$, $v(u-1)\le \exp(-c_\chi(i))$. Let $f : \mathrm{GL}_2(F) \to \mathbb{C}$ lie in `principalSeries2 p χ`: $f$ is locally constant, satisfies $f(\binom{1\ x}{0\ 1}h)=f(h)$ for all $x \in F$, and $f(\mathrm{diag}(a_0,a_1)h)=\chi_0(a_0)\chi_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,f(h)$ for all units $a_0,a_1$. Let $w_0 \in \mathrm{GL}_2(F)$ have matrix $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$, let $\theta$ be an additive character of $F$ with values in $\mathbb{C}$ which is trivial on some ball $\{y : v(y)\le\exp k\}$, $k \in \mathbb{Z}$, and is not the trivial character, and let $g \in \mathrm{GL}_2(F)$ be arbitrary. Then, with $F$ carrying its Borel $\sigma$-algebra, for every additive Haar measure $\nu$ on $F$ there are an integer $M_0$, a finite set $S \subseteq \mathbb{Z}$ and a function $c : \mathbb{Z} \to \mathbb{C}$ such that for every $u \in \mathbb{C}$ and every integer $M \ge M_0$ the function $$y \mapsto f(w_0\,n(y)\,g)\cdot\Bigl(\tfrac{\|\det(w_0 n(y) g)\|}{\max(\|(w_0 n(y) g)_{10}\|,\|(w_0 n(y) g)_{11}\|)^2}\Bigr)^{u}\,\theta(y),\qquad n(y)=\tbinom{1\ y}{0\ 1},$$ is integrable on the ball $\{y : v(y)\le \exp M\}$ with respect to $\nu$, and its integral over that ball equals $\sum_{j \in S} c(j)\, q^{\,j u}$. In particular $M_0$, $S$ and $c$ do not depend on $u$.
--
--   This is the stabilisation statement for the truncated Jacquet (Whittaker) integrals along the flat family $f\cdot H^u$ through a vector $f$ of the normalised principal series of $\mathrm{GL}_2(F)$, $H$ being the Iwasawa height $\|\det h\|/\max(\|h_{10}\|,\|h_{11}\|)^2$: beyond a truncation level independent of $u$ the integral is constant in $M$ and is a Laurent polynomial in $q^u$. It is used to construct the regularised Jacquet integral and the Whittaker functional on the principal series, in [`LanglandsTunnell.CubicInduction.exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2`](thm.html#LanglandsTunnell.CubicInduction.exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2) and in [`LanglandsTunnell.CubicInduction.exists_linearMap_stabilised_jacquetIntegral_principalSeries2`](thm.html#LanglandsTunnell.CubicInduction.exists_linearMap_stabilised_jacquetIntegral_principalSeries2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (hθk : ∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → θ y = 1)
    (hθ1 : θ ≠ 1)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      ∃ (M₀ : ℤ) (S : Finset ℤ) (c : ℤ → ℂ), ∀ (u : ℂ) (M : ℤ), M₀ ≤ M →
        IntegrableOn (fun y : p.adicCompletion ℚ =>
            f (w₀ * unipotentGL2 y * g) *
              ((‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                    Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
                  max ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
                    ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ) ^ u * θ y)
          {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M} ν ∧
        ∫ y in {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M},
            f (w₀ * unipotentGL2 y * g) *
              ((‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                    Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
                  max ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
                    ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ) ^ u * θ y ∂ν =
          ∑ j ∈ S, c j * (Ideal.absNorm p.asIdeal : ℂ) ^ ((j : ℂ) * u) := by sorry
