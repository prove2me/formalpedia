-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/11ba58e5-7cf4-552b-a653-db3288942153
-- title:
--   Rationality of the dual local GL₃× GL₂ Rankin–Selberg integral
-- statement:
--   Let $p$ be a height-one prime of $\mathbb Z$ and write $\mathbb Q_p$ for the completion. The data are: a function $W_3$ on $GL_3(\mathbb Q_p)$ which is Whittaker for the inverse $\psi_p^{-1}$ of the standard local additive character, i.e. $W_3(u(x,y,z)g)=\psi_p^{-1}(x+y)W_3(g)$ for the upper unipotent matrices $u(x,y,z)$, is right invariant under some open subgroup, and satisfies a gauge condition: there are $B,C\in\mathbb R$ and $t\in\mathbb N$ with $W_3(h)=0$ unless both $\det\text{-size}(h)\cdot\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2\le B$ and $\mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2\le B$, and $\|W_3(h)\|\le C$ divided by the $t$-th power of the product of those two ratios otherwise (here $\mathrm{lastRowSup}$, $\mathrm{minorSup}$, $\mathrm{detSize}$ are the sup-norms of the last row, of the $2\times2$ minors of the bottom two rows, and the norm of the determinant); a level $b\in\mathbb N$; a uniformiser $\varpi$ of the valuation ring, of valuation $\exp(-1)$ and nonzero in $\mathbb Q_p$. The hypothesis `hβrat` asserts, for every $g_3\in GL_3(\mathbb Q_p)$, every $k_0\in GL_2(\mathbb Q_p)$, every character $\eta$ of $\mathbb Q_p^\times$ of conductor exponent $c\le b$ (trivial on the $c$-th higher units and nontrivial on each lower level), and every Haar measure $\mu_2$ on $GL_2(\mathbb Q_p)$, that the two shell functions on $\mathbb Z\times\mathbb Z$
--   $$A(n)=\int_{|u|=1}\Big(\int_{K_b}W_3\big(\iota(\mathrm{scalarPi}(\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u,1)\,k_0k)\,g_3\big)\,d\mu_2(k)\Big)\eta(u)\,d^\times u$$
--   and its dual analogue $A^\vee$, obtained by replacing $W_3(\,\cdot\,g_3)$ by its dual Whittaker function $h\mapsto W_3(w_3\,{}^t h^{-1}g_3)$ and $k$ by ${}^tk^{-1}$, each satisfy a two-variable rational recurrence: there are $N_1\in\mathbb Z$, polynomials $D_1,D_2$ with $D_i(0)\ne0$ and $M\in\mathbb N$ such that the function vanishes when either coordinate is $<N_1$, and the $D_1\otimes D_2$-convolution of its values at $(N_1+m_1-i,N_1+m_2-l)$ vanishes whenever $M\le m_1$ or $M\le m_2$; here $K_b$ is the local level-one subgroup at $p^b$ and $d^\times u$ is the multiplicative measure attached to the self-dual additive Haar measure. Further data: a partner $w_2$ on $GL_2(\mathbb Q_p)$ which is $\psi_p$-Whittaker on the left for the unipotent subgroup, right invariant under $K_b$, has central character $\omega$, satisfies a polynomial growth bound $\|w_2(\mathrm{diag}(\varpi^m,1)k)\|\le C\,N(p)^{Am}$ for $m\ge0$ and $k$ in the full local level-one subgroup, and satisfies a one-variable rational recurrence of the same shape along those Kirillov shells; and $w_0^p\in GL_2(\mathbb Q_p)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. The conclusion: for every $g_3\in GL_3(\mathbb Q_p)$, every Haar measure $\mu_2$ on $GL_2(\mathbb Q_p)$ and every Haar measure $\mu_{N_2}$ on the image of the unipotent one-parameter subgroup, there exist polynomials $P^\vee,Q^\vee$ with $Q^\vee\ne0$, an integer $m^\vee$ and an abscissa $\sigma_3$ such that for all $s$ with $\Re s>\sigma_3$ the function $g\mapsto W_3(w_3\,{}^t\iota(g)^{-1}g_3)\cdot\big(|\det g|\,w_2(w_0^p\,{}^tg^{-1})\big)\cdot|\det g|^{s-1/2}$ is integrable against $\mu_2$ weighted by the quotient density of the unipotent subgroup, and the local Rankin–Selberg integral $\mathrm{rsLocalIntegral}$ of that pair with $\delta=|\det\,\cdot\,|$ at $s$, multiplied by $Q^\vee(N(p)^{-s})$, equals $N(p)^{m^\vee s}P^\vee(N(p)^{-s})$, where $|\cdot|$ denotes the modulus (normalised absolute value) on $\mathbb Q_p$.
--
--   This is the local theory of Jacquet–Piatetski-Shapiro–Shalika for $GL_3\times GL_2$ at a finite place, in the form: absolute convergence in a right half-plane and rationality in $N(p)^{-s}$, here for the dual Whittaker function attached to a single right translate $W_3(\,\cdot\,g_3)$ and the base partner $w_2$. It supplies the dual half of the two-sided convergence-and-rationality statement covering the whole cyclic space of translates of $W_3$ and the span of translates of the partner.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (b : ℕ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hβrat :
      ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
        letI := localBorel ℚ p
        letI := localGLBorel ℚ p
        haveI := borelSpace_localGLBorel ℚ p
        ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
          let A : ℤ × ℤ → ℂ := fun n =>
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          let Ad : ℤ × ℤ → ℂ := fun n =>
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
            (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
            (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
              ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
                D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) ∧
          (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
            (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Ad n = 0) ∧
            (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
              ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
                D₁.coeff i * D₂.coeff l * Ad (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)))

    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)

    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))

    (hw₂rec : ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        (∀ m : ℤ, m < N₁ →
          w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1),
            D.coeff i *
              w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0))

    (w₀p : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    ∀ g₃ : LocalGL3 p,
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∃ (Pd Qd : Polynomial ℂ) (md : ℤ) (σ₃ : ℝ), Qd ≠ 0 ∧
          ∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g) *
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂base (w₀p * transposeInvN (Fin 2) g)) g) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂base (w₀p * transposeInvN (Fin 2) g)) *
                Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
