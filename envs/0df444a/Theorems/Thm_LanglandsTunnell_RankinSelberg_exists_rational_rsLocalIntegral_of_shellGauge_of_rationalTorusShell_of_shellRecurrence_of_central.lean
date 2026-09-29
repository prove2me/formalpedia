-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
-- name    : LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ce7e13b0-539f-53c2-ade8-cdbbc58ca345
-- title:
--   Rationality in q^{-s} of a local GL₂ Rankin–Selberg integral
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, write $q=N(v)$ for the absolute norm of $v$, and let $\varpi$ lie in the valuation ring of $\mathbb{Q}_v$ with nonzero image $\pi$ of valuation $\exp(-1)$. Let $b\in\mathbb{N}$ and let $K_b$ be an open subgroup of $\mathrm{GL}_2(\mathbb{Q}_v)$ contained in $K_0:=\mathrm{AdelicDock.localLevelOne}(\mathcal{O}_{\mathbb{Q}},\mathbb{Q},v,\top)$ (the pullback along the local embedding into $\mathrm{GL}_2$ of the finite adeles of the level-one subgroup at level $\top$) and containing every $k\in K_0$ all of whose entries of $k-1$ have valuation at most $\exp(-b)$. Let $A,B:\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$, with $A$ right invariant under some open subgroup, $B$ right $K_b$-invariant, and $A(ug)B(ug)=A(g)B(g)$ for every upper unipotent $u=\mathrm{unipotent}(x)$. Put $a_n=\mathrm{scalarPi}(\pi)^{n_2}\,\mathrm{diagZ}(\pi,n_1)=\mathrm{diag}(\pi^{n_2},\pi^{n_2})\,\mathrm{diag}(\pi^{n_1},1)$. Assume: (shell gauge) there are $m_0\in\mathbb{Z}$, $t\in\mathbb{N}$, $C_A\in\mathbb{R}$ with $A(a_nk)=0$ for $k\in K_0$ unless $m_0\le n_1$ and $m_0\le n_2$, and $\|A(a_nk)\|\le C_A q^{t(n_1+n_2)}$ always; (rational torus shells) for every $k_0\in K_0$, every character $\eta$ of $\mathbb{Q}_v^\times$ with $\mathrm{HasConductorExponentAt}$ exponent $c\le b$ (i.e. $\eta$ trivial on the $c$-th higher units and nontrivial on the $m$-th for each $m<c$), and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ for the Borel structure $\mathrm{localGLBorel}$, the array $$\mathrm{Arr}(n)=\int_{|u|=1}\Bigl(\int_{K_b}A\bigl(\mathrm{scalarPi}(\pi)^{n_2}\,\mathrm{diagUnitGL2}(\pi^{n_1}u)\,k_0k\bigr)\,d\mu_2(k)\Bigr)\eta(u)\,du,$$ the outer integral taken for the multiplicative measure obtained by pulling back $\mathrm{mulMeasure}(\mathrm{selfDualHaarAt})$ along $u\mapsto u$, admits $N_1\in\mathbb{Z}$, polynomials $D_1,D_2$ with $D_1(0)\ne0\ne D_2(0)$ and $M\in\mathbb{N}$ such that $\mathrm{Arr}(n)=0$ when $n_1<N_1$ or $n_2<N_1$, and $\sum_{i,l}D_{1,i}D_{2,l}\,\mathrm{Arr}(N_1+m_1-i,\,N_1+m_2-l)=0$ whenever $M\le m_1$ or $M\le m_2$; (central character) $B(\mathrm{diag}(z,z)g)=\omega(z)B(g)$ for a character $\omega$ of $\mathbb{Q}_v^\times$; (growth) $\|B(\mathrm{diagZ}(\pi,m)k)\|\le Cq^{A'm}$ for $m\ge0$, $k\in K_0$, with $C,A'$ real; (shell recurrence) there are $N_1'\in\mathbb{Z}$, $D$ with $D(0)\ne0$ and $M'\in\mathbb{N}$ such that, for every $k\in K_0$, $B(\mathrm{diagZ}(\pi,m)k)=0$ for $m<N_1'$ and $\sum_i D_i\,B(\mathrm{diagZ}(\pi,N_1'+m-i)k)=0$ for $m\ge M'$. Then, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ and every Haar measure $\mu_{N}$ on the image of $\mathrm{unipotentGL2Hom}$, there exist polynomials $P,Q\in\mathbb{C}[X]$ with $Q\ne0$, an integer $m$ and a real $\sigma_2$ such that for all $s$ with $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto A(g)B(g)\,|\det g|^{s-1/2}$ is integrable against $\mu_2$ weighted by the density $\mathrm{HaarQuotient.density}$ of the unipotent subgroup with $\mu_N$, and the resulting integral $\mathrm{RSCarrier.rsLocalIntegral}$ with $\delta(g)=\mathrm{modulus}(\det g)$ satisfies $$\mathrm{rsLocalIntegral}(s,A,B)\cdot Q(q^{-s})=q^{ms}\,P(q^{-s}).$$
--
--   This is the rationality statement for the local Rankin–Selberg integral of a pair $(A,B)$ at a finite place: under a gauge and a two-variable linear recurrence on the torus shells of $A$, a central character, moderate growth and a one-variable recurrence on the shells of $B$, the integral is a rational function of $q^{-s}$ times an integral power of $q^{s}$, on a right half-plane where it converges absolutely. It is used in the construction of the local factors for $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg and Godement–Jacquet integrals occurring in the Langlands–Tunnell step, being cited by the results on rationality of the integrals attached to translates and duals of Whittaker functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.lean

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

open MeasureTheory IsDedekindDomain NumberField
open AutomorphicForm
open UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
    (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hKb : IsOpen (Kb : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hKbK : Kb ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (hKbc : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb)
    (A B : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hA : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion ℚ), A (g * k) = A g)
    (hB : ∀ k ∈ Kb, ∀ g : GL (Fin 2) (v.adicCompletion ℚ), B (g * k) = B g)
    (hAB : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      A (unipotent x * g) * B (unipotent x * g) = A g * B g)

    (hAshell : ∃ (m₀ : ℤ) (t : ℕ) (CA : ℝ), ∀ (dn : ℤ × ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ ≤
        CA * (Ideal.absNorm v.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2)))

    (hArat : ∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      HasConductorExponentAt ℚ v η c → c ≤ b →
      letI := localBorel ℚ v
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let Arr : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Arr n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * Arr (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))

    (ω : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hBcen : ∀ (z : (v.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      B (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * B g)

    (hBgr : ∃ (C A' : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ‖B (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A' * m))

    (hBrec : ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        (∀ m : ℤ, m < N₁ → B (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * B (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) :
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ (P Q : Polynomial ℂ) (m : ℤ) (σ₂ : ℝ), Q ≠ 0 ∧
        ∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (A g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s A B * Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
