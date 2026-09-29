-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero
-- name    : LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/f1e71fe5-755e-5bc9-be12-e728caee5ec5
-- title:
--   Local Rankin–Selberg integral as a Laurent polynomial in q^{-s}
-- statement:
--   Let $K$ be a number field and $v$ a finite place of $\mathcal{O}_K$, and let $\varpi$ be an element of the valuation ring of $F=K_v$ whose image in $F$ is nonzero and has valuation $\exp(-1)$. Let $b$ be a natural number and let $K_b$ be an open subgroup of $\mathrm{GL}_2(F)$ contained in [`AdelicDock.localLevelOne (𝓞 K) K v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_{K,\mathrm{fin}})$ of the level-one subgroup at the unit ideal, and containing every $k$ of that group all of whose entries of $k-1$ have valuation at most $\exp(-b)$. Let $A,B:\mathrm{GL}_2(F)\to\mathbb{C}$ be functions such that $A$ is right invariant under some open subgroup, $B$ is right invariant under $K_b$, and $A(u(x)g)B(u(x)g)=A(g)B(g)$ for all $x\in F$ and $g$, where $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Equip $F$ and $\mathrm{GL}_2(F)$ with their Borel structures and let $\mu_2$, $\mu_{N}$, $\nu$ be Haar measures on $\mathrm{GL}_2(F)$, on the image $N$ of the unipotent homomorphism $x\mapsto u(x)$, and on $F^{\times}$. Assume that for every $k_0$ in the level-one subgroup and every character $\eta:F^{\times}\to\mathbb{C}^{\times}$ having conductor exponent $c\le b$ (that is, $\eta$ is trivial on the $c$-th higher unit set and nontrivial on every higher unit set of smaller index) there is a finite set $T\subseteq\mathbb{Z}\times\mathbb{Z}$ such that for all $(n_1,n_2)\notin T$ $$\int_{|u|=1}\Big(\int_{K_b}A\big(\mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u,1)\,k_0k\big)\,\mathrm{d}\mu_2(k)\Big)\eta(u)\,\mathrm{d}\nu(u)=0 .$$ Then there exist $P\in\mathbb{C}[X]$ and $m\in\mathbb{Z}$ such that for every $s\in\mathbb{C}$ for which $g\mapsto A(g)B(g)\,|\det g|^{s-1/2}$ is integrable against $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ with $\mu_N$, the local integral $\int (A\cdot B)(g)\,|\det g|^{s-1/2}$ against that weighted measure, i.e. [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) with modulus $\delta(g)=|\det g|$, equals $q^{ms}\,P(q^{-s})$ with $q=\mathrm{absNorm}(v)$.
--
--   This is the local mechanism by which Rankin–Selberg integrals at a finite place are Laurent polynomials in $q^{-s}$, rather than merely rational functions, once the torus values of the first factor are of finite type against characters of conductor exponent at most $b$. It is applied, in the two results that cite it, to integrals built from a Whittaker function pulled back along the embedding of $\mathrm{GL}_2$ and a $\mathrm{GL}_2$ Whittaker function of level $\mathfrak{p}^b$, on the primal side and on the transposed (dual) side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero
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
    (A B : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hA : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A (g * k) = A g)
    (hB : ∀ k ∈ Kb, ∀ g : GL (Fin 2) (v.adicCompletion K), B (g * k) = B g)
    (hAB : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
      A (unipotent x * g) * B (unipotent x * g) = A g * B g) :
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
      ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ,
        Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
          (A g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
            (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
            s A B =
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
