-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/6d57749f-40f7-5c26-bd72-79c85d5ba81d
-- title:
--   Torus-shell expansion of a local Rankin–Selberg product integral
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$, and $\varpi$ an element of the valuation ring of $F=K_v$ whose image $\pi$ in $F$ is nonzero and has valuation $\exp(-1)$, i.e. is a uniformiser. Let $b\in\mathbb N$, and let $K_0 =$ [`AdelicDock.localLevelOne (𝓞 K) K v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb A_{K,\mathrm f})$ of the adelic level-one subgroup at the unit ideal. Let $K_b$ be an open subgroup of $\mathrm{GL}_2(F)$ with $K_b\le K_0$ which contains every $k\in K_0$ all of whose matrix entries of $k-1$ have valuation at most $\exp(-b)$. Let $A,B:\mathrm{GL}_2(F)\to\mathbb C$, with $A$ invariant under right translation by some open subgroup and $B$ invariant under right translation by $K_b$; let $\omega:F^\times\to\mathbb C^\times$ be a homomorphism with $B(z\cdot 1_2\, g)=\omega(z)B(g)$ for all $z\in F^\times$, $g\in\mathrm{GL}_2(F)$. Assume the shell sequences of $B$, indexed by $m\mapsto B(\mathrm{diag}(\pi^m,1)k)$ for $k\in K_0$, satisfy: a growth bound $\|B(\mathrm{diag}(\pi^m,1)k)\|\le C\,N(v)^{A'm}$ for all $m\ge 0$ and all $k\in K_0$, with $C,A'$ independent of $m,k$; and, for some $N_1\in\mathbb Z$, $D\in\mathbb C[X]$ with $D(0)\ne 0$ and $M\in\mathbb N$, vanishing $B(\mathrm{diag}(\pi^m,1)k)=0$ for $m<N_1$ together with the linear recurrence $\sum_{i\le \deg D}D_i\,B(\mathrm{diag}(\pi^{N_1+m-i},1)k)=0$ for all $m\ge M$, uniformly in $k\in K_0$. Equip $F$ and $\mathrm{GL}_2(F)$ with their Borel structures. Then for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ and every Haar measure $\nu$ on $F^\times$ there exist $n\in\mathbb N$, elements $k_{0,i}\in K_0$, homomorphisms $\eta_i:F^\times\to\mathbb C^\times$ with exponents $c_{\eta,i}\le b$ such that `HasConductorExponentAt K v` holds for $(\eta_i,c_{\eta,i})$ — that is, $\eta_i$ is trivial on the set of units $u$ with $|u|=1$ and $|u-1|\le \exp(-c_{\eta,i})$ (no second condition when $c_{\eta,i}=0$), and is nontrivial on the corresponding set for every smaller exponent — together with sequences $c_i:\mathbb Z\to\mathbb C$, data $N_1\in\mathbb Z$, $D\in\mathbb C[X]$ with $D(0)\ne0$, $M\in\mathbb N$ and reals $C',A''$, such that every $c_i$ vanishes below $N_1$, satisfies $\sum_{j\le\deg D}D_j\,c_i(N_1+m-j)=0$ for all $m\ge M$, and obeys $\|c_i(m)\|\le C'\,N(v)^{A''\max(m,0)}$, and such that for every pair $(m,s)\in\mathbb Z\times\mathbb Z$, writing $a=(\pi 1_2)^{s}\,\mathrm{diag}(\pi^{m},1)$, $$\nu\{u: |u|=1\}\cdot\int_{K_0}A(ak)B(ak)\,d\mu_2(k)=\sum_i \omega(\pi)^{s}\,c_i(m)\int_{|u|=1}\Bigl(\int_{K_b}A\bigl((\pi 1_2)^{s}\,\mathrm{diag}(\pi^{m}u,1)\,k_{0,i}k\bigr)d\mu_2(k)\Bigr)\eta_i(u)\,d\nu(u),$$ the measure of the unit-valuation set entering as its real value coerced to $\mathbb C$.
--
--   This is the value form of the local Rankin–Selberg shell computation at a finite place: the integral over the local level-one subgroup of a product $AB$, taken over the torus shells $(\pi 1_2)^{s}\mathrm{diag}(\pi^m,1)$, is rewritten as a finite sum of partial-Whittaker-type integrals of $A$ alone against characters of the units of conductor exponent at most $b$, with coefficients inheriting the vanishing, recurrence and growth properties of the shell sequences of $B$. It feeds the rationality statement [`LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central`](thm.html#LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central) for the local Rankin–Selberg integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central
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

    (ω : (v.adicCompletion K)ˣ →* ℂˣ)
    (hBcen : ∀ (z : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)),
      B (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * B g)

    (hBgr : ∃ (C A' : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      ‖B (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A' * m))

    (hBrec : ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
        (∀ m : ℤ, m < N₁ → B (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * B (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ₂.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],
      ∃ (n : ℕ) (k₀ : Fin n → GL (Fin 2) (v.adicCompletion K)) (η : Fin n → ((v.adicCompletion K)ˣ →* ℂˣ)) (cη : Fin n → ℕ)
        (c : Fin n → ℤ → ℂ) (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ) (C' A'' : ℝ),
        (∀ i, k₀ i ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) ∧
        (∀ i, HasConductorExponentAt K v (η i) (cη i) ∧ cη i ≤ b) ∧
        D.eval 0 ≠ 0 ∧
        (∀ i, (∀ m : ℤ, m < N₁ → c i m = 0) ∧
          (∀ m : ℕ, M ≤ m →
            ∑ j ∈ Finset.range (D.natDegree + 1), D.coeff j * c i (N₁ + (m : ℤ) - (j : ℤ)) = 0)) ∧
        (∀ i (m : ℤ), ‖c i m‖ ≤ C' * (Ideal.absNorm v.asIdeal : ℝ) ^ (A'' * ((max m 0 : ℤ) : ℝ))) ∧
        ∀ dn : ℤ × ℤ,
          ((ν {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1}).toReal : ℂ) *
            ∫ k in ((AdelicDock.localLevelOne (𝓞 K) K v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
              A (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ dn.1 * k) *
              B (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ dn.1 * k) ∂μ₂ =
          ∑ i, (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ) : ℂˣ) : ℂ) ^ dn.2 * c i dn.1 *
            ∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.1 * u) * (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ) ∂ν) := by sorry
