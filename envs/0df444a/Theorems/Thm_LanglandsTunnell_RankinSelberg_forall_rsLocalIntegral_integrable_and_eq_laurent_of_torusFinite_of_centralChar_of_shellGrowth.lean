-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/8fd632c0-43f8-5281-85dd-edd045c8ddd5
-- title:
--   Convergence and rationality of local GL₃timesGL₂ Rankin–Selberg integrals
-- statement:
--   Let $p$ be a maximal ideal of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$, with completion $F=\mathbb{Q}_p$ and residue norm $q=N(p)$, and let $\psi_p$ be the standard local additive character. The data are: a function $W_{3}^{\mathrm{base}}$ on $\mathrm{GL}_3(F)$ which is $\psi_p^{-1}$-Whittaker, in the sense that $W(u(x,y,z)g)=\psi_p^{-1}(x+y)W(g)$ for the upper unipotent matrix $u(x,y,z)$, is right-invariant under some open subgroup, is non-zero, and satisfies a gauge bound: there are $B$, $t\in\mathbb{N}$, $C$ with $W_3^{\mathrm{base}}(h)=0$ unless both shell parameters $\|\det h\|\cdot\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $\mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ are $\le B$ (here $\mathrm{lastRowSup}$ is the sup-norm of the bottom row and $\mathrm{minorSup}$ the sup-norm of the $2\times2$ minors of the bottom two rows), and $\|W_3^{\mathrm{base}}(h)\|\le C$ divided by the $t$-th power of the product of these two parameters when they are; a natural number $b$ and a uniformiser $\varpi$ (non-zero image in $F$, valuation $\exp(-1)$); a torus-finiteness hypothesis $h_\beta$ at depth $b$, asserting that for every $g_3\in\mathrm{GL}_3(F)$, $k_0\in\mathrm{GL}_2(F)$, character $\eta$ of $F^\times$ having conductor exponent $c\le b$ (trivial on the $c$-th higher unit group, non-trivial on every earlier one) and every Haar measure on $\mathrm{GL}_2(F)$, all but finitely many pairs $n=(n_1,n_2)\in\mathbb{Z}^2$ give vanishing $\eta$-twisted unit integrals, over units of valuation $1$ against the multiplicative Haar measure obtained from the self-dual additive measure, of the averages over the local level-one subgroup at $p^b$ of $W_3^{\mathrm{base}}\bigl(\iota(\varpi^{n_2}I\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k)g_3\bigr)$ and of the corresponding dual expression $\widetilde{W}(h)=W(w_3\,{}^t h^{-1})$ applied to $x\mapsto W_3^{\mathrm{base}}(xg_3)$ with $k$ replaced by ${}^tk^{-1}$; a non-zero function $w_2^{\mathrm{base}}$ on $\mathrm{GL}_2(F)$ which is $\psi_p$-equivariant for left translation by upper unipotents, right-invariant under the local level-one subgroup at $p^b$, transforms by a character $\omega$ of $F^\times$ under the centre, and satisfies $\|w_2^{\mathrm{base}}(\mathrm{diag}(\varpi^m,1)k)\|\le Cq^{Am}$ for all $m\ge0$ and all $k$ in the level-one subgroup at the unit ideal, for some $C,A$; and $w_{0p}\in\mathrm{GL}_2(F)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. The conclusion asserts that for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every Haar measure $\mu_{N_2}$ on the image of the unipotent one-parameter subgroup, every $w_2$ in the complex span of the right translates of $w_2^{\mathrm{base}}$ and every $W_3$ in the span of the right translates of $W_3^{\mathrm{base}}$, there exist polynomials $P,P^{\vee}\in\mathbb{C}[X]$, integers $m,m^{\vee}$ and reals $\sigma_2,\sigma_3$ such that for $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto W_3(\iota g)w_2(g)|\det g|^{s-1/2}$ is integrable for $\mu_2$ weighted by the quotient density attached to the unipotent subgroup and $\mu_{N_2}$, and for $\mathrm{Re}\,s>\sigma_3$ the same holds with $W_3$ replaced by $\widetilde{W_3}\circ\iota$ and $w_2$ by $g\mapsto|\det g|\,w_2(w_{0p}\,{}^tg^{-1})$; moreover the corresponding local Rankin–Selberg integrals equal $q^{ms}P(q^{-s})$ on $\mathrm{Re}\,s>\sigma_2$ and $q^{m^{\vee}s}P^{\vee}(q^{-s})$ on $\mathrm{Re}\,s>\sigma_3$ respectively.
--
--   This is the local convergence-and-rationality statement for Rankin–Selberg integrals on $\mathrm{GL}_3\times\mathrm{GL}_2$ over a $p$-adic field, formulated at the level of individual vectors: the gauge bound and the shell growth condition supply absolute convergence in a right half-plane, and torus finiteness at depth $b$ forces both integrals to be Laurent polynomials in $q^{-s}$, hence rational with no poles. It feeds the cell-by-cell integrability and rationality statements used in the cubic induction underlying the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth.lean

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

theorem
  LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (b : ℕ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hβ : ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 ∧
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0)

    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)

    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))

    (w₀p : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ w₂ ∈ Submodule.span ℂ
          (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),

          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * w₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g) *
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) :
                        p.adicCompletion ℚ) : ℝ) : ℂ) *
                      w₂ (w₀p * transposeInvN (Fin 2) g)) g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂ =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) :
                      p.adicCompletion ℚ) : ℝ) : ℂ) *
                    w₂ (w₀p * transposeInvN (Fin 2) g)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
