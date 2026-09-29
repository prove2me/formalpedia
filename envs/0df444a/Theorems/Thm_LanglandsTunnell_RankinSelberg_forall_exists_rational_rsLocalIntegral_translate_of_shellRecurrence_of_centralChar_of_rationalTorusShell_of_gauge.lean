-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/97f64912-c54c-5690-b238-5c09d7698160
-- title:
--   Rationality of one local GL₃× GL₂ Rankin–Selberg integral
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and write $F = \mathbb{Q}_p$ for the completion, $q = \mathrm{Nm}(p)$ for the absolute norm, $\psi$ for the local standard additive character `psiLocal` at $p$. Let $W_3 : GL_3(F) \to \mathbb{C}$ satisfy the $\psi^{-1}$-Whittaker law $W_3(u(x,y,z)g) = \psi^{-1}(x+y)W_3(g)$ for the upper unipotent $u(x,y,z)$ of $GL_3$, be invariant under right translation by some open subgroup, and be bounded by a gauge: there are $B$, $t$, $C$ such that, in terms of $a(h) = \lVert\det h\rVert \cdot \mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $c(h) = \mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ (suprema of the norms of the bottom-row entries and of the three $2\times 2$ minors of the bottom two rows), $W_3(h) = 0$ unless $a(h) \le B$ and $c(h) \le B$, and $\lVert W_3(h)\rVert \le C/(a(h)c(h))^t$ on that region. Let $b \in \mathbb{N}$ and let $\varpi$ be an element of the valuation ring whose image in $F$ is nonzero of valuation $\exp(-1)$. Assume the rationality hypothesis `hβrat`: for every $g_3 \in GL_3(F)$, every $k_0 \in GL_2(F)$, every character $\eta : F^\times \to \mathbb{C}^\times$ with conductor exponent $c \le b$ in the sense of `HasConductorExponentAt` (trivial on the $c$-th higher unit set, nontrivial on every earlier one), and every Haar measure $\mu_2$ on $GL_2(F)$, the two arrays on $\mathbb{Z}\times\mathbb{Z}$ obtained by integrating, over the units of valuation $1$ against $\eta$ and the multiplicative measure attached to the self-dual additive Haar measure, the $\mu_2$-integral over the local level-one subgroup of level $p^b$ of $W_3(\iota(\mathrm{scalarPi}(\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u,1)\,k_0k)g_3)$, respectively of the dual Whittaker function $x \mapsto W_3(w_3\,{}^{t}x^{-1}g_3)$ at the same point with $k$ replaced by ${}^{t}k^{-1}$, each admit $N_1 \in \mathbb{Z}$, polynomials $D_1,D_2$ with nonvanishing constant term and $M \in \mathbb{N}$ such that the array vanishes when either index is $< N_1$ and the corresponding double $D_1 \otimes D_2$ recurrence holds whenever $m_1 \ge M$ or $m_2 \ge M$. Let $w_2 : GL_2(F) \to \mathbb{C}$ satisfy $w_2(u(x)g) = \psi(x)w_2(g)$, be invariant under right translation by the local level-one subgroup of level $p^b$, have central character $\omega : F^\times \to \mathbb{C}^\times$, satisfy $\lVert w_2(\mathrm{diag}(\varpi^m,1)k)\rVert \le Cq^{Am}$ for all $m \ge 0$ and all $k$ in the level-one subgroup at $\top$, and satisfy a one-variable recurrence there: for some $N_1$, some $D$ with $D(0) \ne 0$ and some $M$, the shell values vanish for $m < N_1$ and the $D$-recurrence holds for $m \ge M$, uniformly in $k$. Then for every $g_3 \in GL_3(F)$, every Haar measure $\mu_2$ on $GL_2(F)$ (with its Borel structure) and every Haar measure $\mu_{N_2}$ on the range of the unipotent homomorphism into $GL_2(F)$, there are polynomials $P,Q \in \mathbb{C}[X]$ with $Q \ne 0$, an integer $m$ and a real $\sigma_2$ such that for all $s$ with $\operatorname{Re} s > \sigma_2$ the function $g \mapsto W_3(\iota(g)g_3)\,w_2(g)\,\lvert\det g\rvert^{s-1/2}$ is integrable for $\mu_2$ weighted by the quotient density of the unipotent subgroup relative to $\mu_{N_2}$, and the resulting local integral `rsLocalIntegral` satisfies $\Psi(s)\,Q(q^{-s}) = q^{ms}P(q^{-s})$.
--
--   This is the local Rankin–Selberg integral for $GL_3 \times GL_2$ at a finite place: absolute convergence in a right half-plane together with rationality in $q^{-s}$, stated for a single right translate $W_3(\iota(\cdot)g_3)$ of the $GL_3$ Whittaker function and for the given $GL_2$ partner $w_2$. It is the primal half used in the two-sided statement [`LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_and_dual_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge`](thm.html#LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_and_dual_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge), which treats simultaneously the whole cyclic space of translates and the dual integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
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
                (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) :
    ∀ g₃ : LocalGL3 p,
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∃ (P Q : Polynomial ℂ) (m : ℤ) (σ₂ : ℝ), Q ≠ 0 ∧
          ∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃base (iotaGL g * g₃) * w₂base g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃base (iotaGL g * g₃)) w₂base * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
