-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/bf359930-8654-5520-b851-79a20ce02f72
-- title:
--   Local Rankin–Selberg integral of a unipotent-supported bump integrand
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and give $\mathrm{GL}_2(\mathbb{Q}_p)$, for $\mathbb{Q}_p$ the completion of $\mathbb{Q}$ at $p$, its Borel $\sigma$-algebra. Fix a Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$, a Haar measure $\mu_{N}$ on the subgroup $N$ given by the image of the homomorphism $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ from $\mathbb{Q}_p$ (written multiplicatively) into $\mathrm{GL}_2(\mathbb{Q}_p)$, and a subgroup $U \le \mathrm{GL}_2(\mathbb{Q}_p)$ whose underlying set is compact and open and which satisfies $\mathrm{modulus}(\det u) = 1$ for all $u \in U$, where $\mathrm{modulus}(a)$ is the scaling factor of the Haar measure of $\mathbb{Q}_p$ under multiplication by $a$ (and $0$ for $a = 0$). Then there is a real $c > 0$, depending only on these data, such that for every $s \in \mathbb{C}$ and all functions $W, F : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ for which the product $WF$ is invariant under left translation by the matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, vanishes at every $g$ not of the form $\begin{pmatrix}1&x\\0&1\end{pmatrix}u$ with $u \in U$, and is constant equal to $W(1)F(1)$ on $U$, one has
--   $$\int_{\mathrm{GL}_2(\mathbb{Q}_p)} W(g)F(g)\,\mathrm{modulus}(\det g)^{\,s - 1/2}\, d\bigl(\mu_2 \cdot \mathrm{density}(N,\mu_{N})\bigr)(g) = c\,W(1)F(1),$$
--   the integral being that of the project's local Rankin–Selberg carrier: $\mu_2$ weighted by the quotient density attached to $N$ and $\mu_{N}$. In particular $c$ is independent of $s$, $W$ and $F$.
--
--   This is the local (at a finite place of $\mathbb{Q}$) evaluation of a $\mathrm{GL}_2 \times \mathrm{GL}_2$ Rankin–Selberg integral at a test vector whose integrand is a bump supported on a single unipotent-by-compact-open cell, the constant $c$ being the mass of that cell in the quotient. It is used in the construction of $\mathrm{GL}_3$ Whittaker test vectors, where local integrals of this shape are combined to produce a nonvanishing value of the global Rankin–Selberg integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul
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
        (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          W (unipotent x * g) * F (unipotent x * g) = W g * F g) →
        (∀ g : GL (Fin 2) (p.adicCompletion ℚ), W g * F g ≠ 0 →
          ∃ (x : p.adicCompletion ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)), u ∈ U ∧ g = unipotent x * u) →
        (∀ u ∈ U, W u * F u = W 1 * F 1) →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s W F = (c : ℂ) * (W 1 * F 1) := by sorry
