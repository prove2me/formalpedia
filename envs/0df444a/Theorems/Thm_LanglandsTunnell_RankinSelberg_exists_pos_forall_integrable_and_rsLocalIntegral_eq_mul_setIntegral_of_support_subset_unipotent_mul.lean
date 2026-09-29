-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/2ee127d4-0fc1-5c77-aed9-4ee9299e8a22
-- title:
--   Local Rankin–Selberg integral supported on a unipotent orbit of U
-- statement:
--   Let $p$ be a maximal ideal of the ring of integers of $\mathbb Q$, and equip $\mathrm{GL}_2$ of the completion $\mathbb Q_p =$ `p.adicCompletion ℚ` with its Borel $\sigma$-algebra. Let $\mu_2$ be a Haar measure on $\mathrm{GL}_2(\mathbb Q_p)$, let $N$ denote the range of the homomorphism $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ from the additive group of $\mathbb Q_p$ (written multiplicatively) into $\mathrm{GL}_2(\mathbb Q_p)$, and let $\mu_{N}$ be a Haar measure on $N$. Let $U$ be a subgroup of $\mathrm{GL}_2(\mathbb Q_p)$ whose underlying set is compact and open and on which $\mathrm{modulus}(\det u) = 1$, where $\mathrm{modulus}$ is the distributive Haar character of $\mathbb Q_p$ at a nonzero scalar (and $0$ at $0$). Then there is a real $c > 0$ such that for every $s \in \mathbb C$ and all $W, F : \mathrm{GL}_2(\mathbb Q_p) \to \mathbb C$ for which the product $g \mapsto W(g)F(g)$ is measurable, is integrable on $U$ for $\mu_2$, satisfies $W(n(x)g)F(n(x)g) = W(g)F(g)$ for all $x \in \mathbb Q_p$ and all $g$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and vanishes at every $g$ not of the form $n(x)u$ with $u \in U$, the following hold: the function $g \mapsto W(g)F(g)\,\mathrm{modulus}(\det g)^{s-1/2}$ is integrable for $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to $N$ and $\mu_N$ (the explicit compact-exhaustion weight normalised along the $N$-orbits), and the local Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16), namely the integral of that function against this weighted measure, equals $c \int_U W(u)F(u)\,d\mu_2(u)$. In particular $c$ depends only on $p$, $\mu_2$, $\mu_N$ and $U$, and the value of the integral is independent of $s$.
--
--   This is the evaluation of a local Rankin–Selberg integral over $N \backslash \mathrm{GL}_2(\mathbb Q_p)$ in the degenerate case where the integrand is supported on the single unipotent orbit $N \cdot U$ of a compact open subgroup $U$ of determinant modulus one: absolute convergence holds and the integral collapses to a positive multiple of the integral of $W \cdot F$ over $U$, with no dependence on $s$. It is used in the corresponding evaluation for the dual long Weyl element against a smoothed bump supported on a unit shell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure]
      (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
      (_hUc : IsCompact (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
      (_hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
      (_hUdet : ∀ u ∈ U,
        modulus ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1),
    ∃ c : ℝ, 0 < c ∧
      ∀ (s : ℂ) (W F : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        Measurable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W g * F g) →
        IntegrableOn (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W g * F g)
          (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ →
        (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          W (unipotent x * g) * F (unipotent x * g) = W g * F g) →
        (∀ g : GL (Fin 2) (p.adicCompletion ℚ), W g * F g ≠ 0 →
          ∃ (x : p.adicCompletion ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)), u ∈ U ∧ g = unipotent x * u) →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W g * F g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s W F =
          (c : ℂ) * ∫ u in (U : Set (GL (Fin 2) (p.adicCompletion ℚ))), W u * F u ∂μ₂ := by sorry
