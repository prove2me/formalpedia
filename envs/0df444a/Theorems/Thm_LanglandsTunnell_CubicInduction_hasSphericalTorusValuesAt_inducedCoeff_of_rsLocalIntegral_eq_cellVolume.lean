-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume
-- name    : LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/0e415f5d-747c-56e1-95a8-0e320186882e
-- title:
--   Spherical torus values from Rankin–Selberg local integrals
-- statement:
--   Let $K$ be a number field of degree at most $3$ over $\mathbb{Q}$, equipped with an integral $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$, let $\mu:(\mathbb{A}_K)^{\times}\to\mathbb{C}^{\times}$ be a character of the idele units, let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, let $c\in\mathbb{N}$, and let $W:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ satisfy: $W(u(x,y,z)g)=\psi_v^{-1}(x+y)\,W(g)$ for all upper unipotent $u(x,y,z)$ and all $g$, where $\psi_v$ is the standard local additive character `psiLocal ℚ v`; $W(gk)=W(g)$ for all $g$ and all $k$ in `congruenceK1 (𝓞 ℚ) ℚ v c`, i.e. $k$ with all entries of $k$ and $k^{-1}$ of valuation $\le 1$ and with $v(k_{20}),v(k_{21}),v(k_{22}-1)\le q^{-c}$; and $W(1)=1$. Assume further the following: for every uniformiser $\pi$ of $\mathbb{Q}_v$ (the image of an element of the valuation ring, nonzero, of valuation $\exp(-1)$), all $a_1,a_2\in\mathbb{C}$ with $a_1a_2\ne 0$, every $W_2:\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ with $W_2(u(x)g)=\psi_v(x)W_2(g)$, right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), with $W_2(1)=1$, $W_2(g\cdot\pi I)=\bigl(a_1a_2/\mathrm{N}v\bigr)W_2(g)$ and $W_2(\mathrm{diag}(\pi^m,1))=$ `torusFactor` $(\mathrm{N}v,a_1+a_2,a_1a_2/\mathrm{N}v,m)$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ (for the Borel structure `localGLBorel`) and Haar measure $\mu_N$ on the range of `unipotentGL2Hom`, there is $\sigma_2\in\mathbb{R}$ such that for all $s$ with $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto W(\iota(g))W_2(g)|\det g|^{s-1/2}$ is integrable for $\mu_2$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup with respect to $\mu_N$, and the corresponding local integral `rsLocalIntegral` with $\delta=|\det\cdot|$, times the values of `inducedEulerPoly ℚ (inducedCoeff K μ) v` at $a_1\,\mathrm{N}v^{-(s+1/2)}$ and at $a_2\,\mathrm{N}v^{-(s+1/2)}$, equals the volume, for that weighted measure, of the cell $\{g=nk\}$ with $n$ in the unipotent subgroup and $k\in$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), viewed as a complex number. Here $\iota$ is the embedding `iotaGL` of $\mathrm{GL}_2$ in the upper left block of $\mathrm{GL}_3$, $\mathrm{N}v$ is the absolute norm of $v$, and `inducedCoeff K μ` sends a prime $\mathfrak{P}$ of $\mathcal{O}_K$ to $\mu$ of the uniformiser idele at $\mathfrak{P}$ when $\mu$ is unramified at $\mathfrak{P}$, and to $0$ otherwise. The conclusion is `HasSphericalTorusValuesAt (inducedCoeff K μ) v W`: writing $h_n$ for the values of `sphericalTorusValue` at the coefficients $e_1,e_2,e_3$ of `inducedEulerPoly ℚ (inducedCoeff K μ) v`, one has $W(\mathrm{iotaTorusLocal}\ v\ n)=\mathrm{N}v^{-n}h_n$ for all $n$, and $W(\mathrm{twoRowPointLocal}\ v\ k_1\,(k_2+1))=\mathrm{N}v^{-k_1}\bigl(h_{k_1}h_{k_2+1}-h_{k_1+1}h_{k_2}\bigr)$ whenever $k_2+1\le k_1$.
--
--   This is the local Rankin–Selberg step in the cubic induction: the values of a normalised, $K_1(\mathfrak{p}_v^c)$-invariant Whittaker function on $\mathrm{GL}_3(\mathbb{Q}_v)$ at the torus points and at the two-row points are pinned down by the requirement that its local integrals against all $\mathrm{GL}_2$ Whittaker functions with prescribed Hecke parameters be the reciprocal of the product of two induced Euler factors. It is used in the construction of a vector in the $\mathrm{GL}_3$ cyclic subspace at level $K_1$ with the prescribed torus values attached to a cubic induction datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
  LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K ≤ 3) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (c : ℕ) (W : LocalGL3 v → ℂ) (hψ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    (hW : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g, W (g * k) = W g) (hW1 : W 1 = 1)
    (hid : ∀ {ϖ : v.adicCompletionIntegers ℚ}
      (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) →
      ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
      (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
      (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
      (hW₂1 : W₂ 1 = 1)
      (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
          a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
      (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
        torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∃ σ₂ : ℝ,
        (∀ s : ℂ, σ₂ < s.re →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * W₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) W₂ *
              (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                  2))) *
              (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                  2))) =
            (((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
                {g : GL (Fin 2) (v.adicCompletion ℚ) |
                  ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ))) :
    HasSphericalTorusValuesAt (inducedCoeff K μ) v W := by sorry
