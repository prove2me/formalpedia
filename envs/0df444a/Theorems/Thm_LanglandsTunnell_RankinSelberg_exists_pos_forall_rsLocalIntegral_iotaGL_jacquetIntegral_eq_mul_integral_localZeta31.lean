-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_iotaGL_jacquetIntegral_eq_mul_integral_localZeta31
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_iotaGL_jacquetIntegral_eq_mul_integral_localZeta31
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/033bbaa5-ef57-5a84-a974-33e71071ce56
-- title:
--   Unfolding the GL₃timesGL₂ local integral at a principal-series section
-- statement:
--   Fix a prime $p$ of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_p$ for the completion at $p$ and equip $F$ and $\mathrm{GL}_2(F)$ with their Borel structures. Let $\mu_2$ be a Haar measure on $\mathrm{GL}_2(F)$, $\mu_N$ a Haar measure on the subgroup $N \subset \mathrm{GL}_2(F)$ given by the image of $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$, $\tau$ a Haar measure on $F^\times$ and $\nu$ an additive Haar measure on $F$. Then there is a real $c > 0$, depending only on these measures, such that for every additive character $\theta$ of $F$ with values in $\mathbb{C}$, every $W \colon \mathrm{GL}_3(F) \to \mathbb{C}$ with $W\!\left(\begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix} g\right) = \theta(x+y) W(g)$ for all $x,y,z \in F$ and $g$, and invariant under right translation by some open subgroup of $\mathrm{GL}_3(F)$, every pair $\chi = (\chi_0,\chi_1)$ of homomorphisms $F^\times \to \mathbb{C}^\times$, every $f$ in the principal series `principalSeries2` attached to $\chi$ (locally constant, invariant on the left under upper unipotents, and transforming under the diagonal torus by $\chi$ times the half-modulus), every $w_0 \in \mathrm{GL}_2(F)$ with underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and every $s \in \mathbb{C}$, the following holds. Assume that $g \mapsto W(\iota g)\,f(w_0 g)\,|\det g|^{s-1/2}$ is $\mu_2$-integrable, where $\iota$ is the block embedding $g \mapsto \mathrm{diag}(g,1)$ of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ and $|\cdot|$ is the modulus of $F$ (the scaling factor of Haar measure, $0$ at $0$). Then, first, $g \mapsto W(\iota g)\left(\int_F f(w_0\, u(y)\, g)\,\theta(y)\,d\nu(y)\right)|\det g|^{s-1/2}$, with $u(y) = \begin{pmatrix}1&y\\0&1\end{pmatrix}$, is integrable for $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ relative to $\mu_N$ (an explicit density realising integration over $N \backslash \mathrm{GL}_2(F)$); and, second, the Rankin–Selberg local integral $\int W(\iota g)\left(\int_F f(w_0 u(y) g)\theta(y)\,d\nu(y)\right)|\det g|^{s-1/2}$ against that weighted measure equals $$c \int_F f(w_0 u(y)) \left(\int_{F^\times} \chi_0(a)\,|a|^{s-1}\, Z(s, W, \chi_1)\bigl(\iota(\mathrm{diag}(1,a)\,u(y))\bigr) d\tau(a)\right) d\nu(y),$$ where $Z(s,W,\chi_1)(h) = \int_{F^\times}\left(\int_F W(\iota(\mathrm{diag}(a,1))\,n^-(x)\,h)\,d\nu(x)\right)\chi_1(a)\,|a|^{s-1}\,d\tau(a)$ is the $\mathrm{GL}_3 \times \mathrm{GL}_1$ zeta integral `localZeta31`.
--
--   This is the unfolding step in the proof of multiplicativity of the local Rankin–Selberg $\gamma$-factor for $\mathrm{GL}_3 \times \mathrm{GL}_2$ when the $\mathrm{GL}_2$ datum is a principal series, as in Jacquet–Piatetski-Shapiro–Shalika: the quotient integral over $N \backslash \mathrm{GL}_2(F)$ of the Whittaker function against the Jacquet integral of a section is rewritten, in Bruhat coordinates, as an integral of $\mathrm{GL}_3 \times \mathrm{GL}_1$ zeta integrals twisted by $\chi_0$. It feeds the construction of the primal and dual middle data used in the cubic-induction functional equations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_iotaGL_jacquetIntegral_eq_mul_integral_localZeta31.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_iotaGL_jacquetIntegral_eq_mul_integral_localZeta31
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure]
      (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
      ∀ (θ : AddChar (p.adicCompletion ℚ) ℂ)
        (W : LocalGL3 p → ℂ) (_hW : IsGL3PsiWhittakerFn θ W)
        (_hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
        (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
        (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (_hf : f ∈ principalSeries2 p χ)
        (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
        (_hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
        (s : ℂ),
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W (iotaGL g) * f (w₀ * g)) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2)) μ₂ →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W (iotaGL g) * (∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂ν)) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) (fun g => ∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂ν) =
          c * ∫ y, f (w₀ * unipotentGL2 y) *
            (∫ a, ((χ 0 a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) *
              localZeta31 p τ ν W (χ 1) s (iotaGL (diagUnits2 1 a * unipotentGL2 y)) ∂τ) ∂ν := by sorry
