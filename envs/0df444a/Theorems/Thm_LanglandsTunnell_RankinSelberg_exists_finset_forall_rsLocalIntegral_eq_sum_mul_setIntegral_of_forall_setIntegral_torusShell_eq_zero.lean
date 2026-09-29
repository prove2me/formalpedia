-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero
-- name    : LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/e4ee45a3-11c7-5488-b467-4c71e6577091
-- title:
--   Finite shell expansion of a local Rankin–Selberg integral
-- statement:
--   Let $K$ be a number field and $v$ a finite place of $K$, with completion $F=K_v$, and let $\varpi$ lie in the valuation ring with image $\pi\in F$ satisfying $\pi\neq 0$ and $|\pi|=\exp(-1)$, i.e. $\pi$ is a uniformiser. Let $b\in\mathbb N$ and let $K_b$ be an open subgroup of $\mathrm{GL}_2(F)$ contained in [`AdelicDock.localLevelOne (𝓞 K) K v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb A_K^f)$ of the finite level-one group of the unit ideal, and containing every element $k$ of that group all of whose entries of $k-1$ have valuation $\le\exp(-b)$. Let $A:\mathrm{GL}_2(F)\to\mathbb C$ be invariant under right translation by some open subgroup. With $F$ and $\mathrm{GL}_2(F)$ carrying their Borel structures, fix Haar measures $\mu_2$ on $\mathrm{GL}_2(F)$, $\mu_{N}$ on the image $N$ of $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and $\nu$ on $F^\times$. Assume the following torus finiteness: for every $k_0$ in the level-one group, every homomorphism $\eta:F^\times\to\mathbb C^\times$ and every $c\le b$ such that $\eta$ is trivial on the units $u$ with $|u|=1$ and ($c=0$ or $|u-1|\le\exp(-c)$) while being nontrivial on each lower such level $m<c$, there is a finite $T\subset\mathbb Z^2$ with
--   $$\int_{|u|=1}\Big(\int_{K_b}A\big(\mathrm{diag}(\pi,\pi)^{n_2}\,\mathrm{diag}(\pi^{n_1}u,1)\,k_0k\big)\,d\mu_2(k)\Big)\eta(u)\,d\nu(u)=0$$
--   for all $(n_1,n_2)\notin T$. Then there are a finite $T\subset\mathbb Z^2$ and constants $c_{d,n}\in\mathbb C$, chosen independently of $B$ and $s$, such that for every $B:\mathrm{GL}_2(F)\to\mathbb C$ invariant under right translation by $K_b$ with $A(n(x)g)B(n(x)g)=A(g)B(g)$ for all $x\in F$, $g\in\mathrm{GL}_2(F)$, and every $s\in\mathbb C$ for which $g\mapsto A(g)B(g)\,\|\det g\|^{s-1/2}$ is integrable against $\mu_2$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ (the normalising density used to compute integrals over $N\backslash\mathrm{GL}_2(F)$), the local integral
--   $$\int A(g)B(g)\,\|\det g\|^{s-1/2}$$
--   against that weighted measure equals
--   $$\sum_{(d,n)\in T}c_{d,n}\,(\mathrm{N}v)^{-(d+2n)s}\int_{K_0}A\big(\mathrm{diag}(\pi,\pi)^{n}\mathrm{diag}(\pi^{d},1)k\big)B\big(\mathrm{diag}(\pi,\pi)^{n}\mathrm{diag}(\pi^{d},1)k\big)\,d\mu_2(k)$$
--   where $K_0$ is the level-one group, $\mathrm{N}v$ the absolute norm of the prime of $v$, and $\|\cdot\|$ the module of $F$.
--
--   This is the local Rankin–Selberg integral of Jacquet–Piatetski-Shapiro–Shalika, expressed in Iwasawa coordinates: torus finiteness of the first factor collapses the integral to a finite sum of shell integrals over $K_0$, so that the dependence on $s$ is through the monomials $(\mathrm{N}v)^{-(d+2n)s}$ and the dependence on the second factor is through finitely many linear functionals supported on compact sets. It is used in the analysis of the dual local integral, where one follows the integral along families of second factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
  LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (Kb : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hKb : IsOpen (Kb : Set (GL (Fin 2) (v.adicCompletion K))))
    (hKbK : Kb ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hKbc : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb)
    (A : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hA : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A (g * k) = A g) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],
      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →
      ∃ (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ),
        ∀ (B : GL (Fin 2) (v.adicCompletion K) → ℂ),
          (∀ k ∈ Kb, ∀ g : GL (Fin 2) (v.adicCompletion K), B (g * k) = B g) →
          (∀ (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
            A (unipotent x * g) * B (unipotent x * g) = A g * B g) →
          ∀ s : ℂ,
            Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
                (fun g : GL (Fin 2) (v.adicCompletion K) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
                s A B =
              ∑ dn ∈ T, c dn * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((dn.1 + 2 * dn.2 : ℤ) : ℂ) * s) *
                ∫ k in ((AdelicDock.localLevelOne (𝓞 K) K v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
                    Set (GL (Fin 2) (v.adicCompletion K))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 *
                      diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ dn.1 * k) *
                    B (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 *
                      diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ dn.1 * k) ∂μ₂ := by sorry
