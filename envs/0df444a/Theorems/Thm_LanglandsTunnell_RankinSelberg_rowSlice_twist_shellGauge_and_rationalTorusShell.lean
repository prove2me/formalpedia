-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_rowSlice_twist_shellGauge_and_rationalTorusShell
-- name    : LanglandsTunnell.RankinSelberg.rowSlice_twist_shellGauge_and_rationalTorusShell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/c3c10898-03cb-589f-b9b5-9680d09a9d2e
-- title:
--   Shell gauge and rational torus shells for twisted row slices
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$ and an element $\varpi$ of the valuation ring of the completion $\mathbb Q_p :=$ `p.adicCompletion ℚ` whose image in $\mathbb Q_p$ is non-zero and has valuation $\exp(-1)$, i.e. a uniformiser. Let $\Phi : M_2(\mathbb Q_p) \to \mathbb C$ be locally constant with compact support and let $\chi : \mathbb Q_p^\times \to \mathbb C^\times$ be a locally constant multiplicative homomorphism. Put $A(g) := \bigl(\int_{\mathbb Q_p} \psi_p(x)\,\Phi(n(x)g)\,dx\bigr)\cdot\chi(\det g)$ for $g \in GL_2(\mathbb Q_p)$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ is `unipotent x`, $\psi_p$ is the local component `psiLocal` of the standard additive character, and the integral is against `selfDualHaarAt`, the additive Haar measure giving $\mathcal O_p$ mass $N(p)^{-\ell/2}$ with $\ell$ the level of $\psi_p$. Three assertions are made. First, some open subgroup $U \le GL_2(\mathbb Q_p)$ satisfies $A(gk) = A(g)$ for all $k \in U$ and all $g$. Second, there are $m_0 \in \mathbb Z$, $t \in \mathbb N$ and $C_A \in \mathbb R$ such that, for every pair $(d_1,d_2) \in \mathbb Z^2$ and every $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the preimage under the local embedding `localEmbed` of the finite-adelic level-one subgroup at the unit ideal), writing $g_{d_1,d_2} := \mathrm{diag}(\varpi,\varpi)^{d_2}\,\mathrm{diag}(\varpi^{d_1},1)\,k$ in the notation `scalarPi`, `diagZ`, one has $A(g_{d_1,d_2}) = 0$ unless $m_0 \le d_1$ and $m_0 \le d_2$, and in all cases $\|A(g_{d_1,d_2})\| \le C_A\,N(p)^{t(d_1+d_2)}$ with $N(p) =$ `Ideal.absNorm p.asIdeal`. Third, for every $b \in \mathbb N$, every subgroup $K_b$ contained in that level-one subgroup, every $k_0$ in it, every multiplicative character $\eta : \mathbb Q_p^\times \to \mathbb C^\times$ and every $c \in \mathbb N$ with $c \le b$ such that $\eta$ is trivial on the higher unit set of level $c$ (units $u$ with $v(u)=1$ and, if $c>0$, $v(u-1)\le \exp(-c)$) and non-trivial on each higher unit set of level $m<c$, and for every Haar measure $\mu_2$ on $GL_2(\mathbb Q_p)$ for the Borel structure `localGLBorel`, consider the array $\mathrm{Arr}(n_1,n_2) := \int_{v(u)=1}\bigl(\int_{K_b} A\bigl(\mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u,1)\,k_0k\bigr)\,d\mu_2(k)\bigr)\eta(u)\,du$, the outer measure being the pullback along $u \mapsto u$ of the multiplicative measure `mulMeasure (selfDualHaarAt ℚ p)` and $\mathrm{diag}(\cdot,1)$ being `diagUnitGL2`. Then there exist $N_1 \in \mathbb Z$, polynomials $D_1, D_2 \in \mathbb C[X]$ with $D_1(0) \ne 0$ and $D_2(0) \ne 0$, and $M \in \mathbb N$, such that $\mathrm{Arr}(n) = 0$ whenever $n_1 < N_1$ or $n_2 < N_1$, and such that for all $m_1, m_2 \in \mathbb N$ with $M \le m_1$ or $M \le m_2$, $\sum_{i,l} D_1[i]\,D_2[l]\,\mathrm{Arr}(N_1+m_1-i,\,N_1+m_2-l) = 0$, the sums running over $i \le \deg D_1$ and $l \le \deg D_2$.
--
--   The function $A$ is the row slice of a Schwartz–Bruhat function $\Phi$ on $M_2(\mathbb Q_p)$ against the local additive character, twisted by $\chi \circ \det$; the three conclusions are exactly the right-invariance, torus-shell gauge and separated-rationality inputs required by the Rankin–Selberg rationality core. It is used in the construction of rational shifted Godement–Jacquet zeta integrals against unramified Whittaker data, via [`LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift`](thm.html#LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_rowSlice_twist_shellGauge_and_rationalTorusShell.lean

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

theorem LanglandsTunnell.RankinSelberg.rowSlice_twist_shellGauge_and_rationalTorusShell
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    let A : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), A (g * k) = A g) ∧
      (∃ (m₀ : ℤ) (t : ℕ) (CA : ℝ), ∀ (dn : ℤ × ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ ≤
        CA * (Ideal.absNorm p.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2))) ∧
      (∀ (b : ℕ) (Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), Kb ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ → ∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let Arr : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                A (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Arr n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * Arr (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) := by sorry
