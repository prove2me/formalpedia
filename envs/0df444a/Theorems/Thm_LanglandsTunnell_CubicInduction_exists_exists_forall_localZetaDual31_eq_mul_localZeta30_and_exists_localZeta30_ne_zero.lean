-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_exists_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero
-- name    : LanglandsTunnell.CubicInduction.exists_exists_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/4d7bc33f-27a3-5b53-bf4f-fa95336599d8
-- title:
--   Stable local functional equation under highly ramified twists
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, let $\psi_v$ be the additive character of $\mathbb{Q}_v$ inverse to the standard one [`NumberField.StandardAddChar.psiLocal`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), and let $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy: $W(u(x,y,z)g) = \psi_v(x+y)W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$; $W(1)=1$; the space of $\psi_v$-Whittaker functionals on the span `gl3CyclicSubspace W` of the right translates of $W$, with its right-translation action, has rank at most $1$ over $\mathbb{C}$; every nonzero $F$ in that span generates $W$ back, i.e. $W \in$ `gl3CyclicSubspace F`; $W$ is right invariant under some open subgroup $U_v \le \mathrm{GL}_3(\mathbb{Q}_v)$; for every open subgroup $U_v$ there is a finite set $B$ of functions whose $\mathbb{C}$-span contains every right $U_v$-invariant member of `gl3CyclicSubspace W`; and $W(\mathrm{diag}(t,t,t)\,h) = \omega_v(t)W(h)$ for a homomorphism $\omega_v : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ with $|\omega_v| = 1$. Then there is $c_0 \ge 1$ in $\mathbb{N}$ such that for every character $\tau : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ and every $c \ge c_0$ with $\tau$ of conductor exponent $c$ (trivial on the $c$-th higher unit group `higherUnitsAt` and nontrivial on each earlier one) and $|\tau(\varpi_v)| = 1$ at the uniformizer unit, there are real abscissae $\sigma_0, \sigma_1$, independent of the group variable, such that for every $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ there is $P : \mathbb{C} \to \mathbb{C}$ of the form $P(s) = Q\bigl(N(v)^{-s}\bigr)N(v)^{ms}$ with $Q \in \mathbb{C}[X]$ and $m \in \mathbb{N}$ for which: the integrand $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,|a|^{s-1}$ is integrable against the measure obtained from the self-dual Haar measure of $\mathbb{Q}_v$ (Borel $\sigma$-algebra) by removing $0$, dividing by the modulus and pulling back along $\mathbb{Q}_v^\times \hookrightarrow \mathbb{Q}_v$, whenever $\sigma_0 < \operatorname{Re} s$, and then `localZeta30` equals $P(s)$; the corresponding double integrand for `dualWhittakerFn3 W`, character $\tau^{-1}$ and argument `weylPrime3` $\cdot$ `transposeInv3` $g$ is integrable on the product with the self-dual Haar measure whenever $\sigma_1 < \operatorname{Re} s$; and for all $s$ with $\sigma_1 < \operatorname{Re}(1-s)$, $$\mathrm{localZetaDual31}(1-s, g) = \omega_v(-1)\tau(-1)\,\varepsilon(\omega_v\tau)\,\varepsilon(\tau)^2\,N(v)^{3c(1/2-s)}\,P(s),$$ with $\varepsilon =$ `stdRootNumberAt ℚ v`. Moreover some $g$ and some $s$ with $\sigma_0 < \operatorname{Re} s$ give `localZeta30` $\ne 0$.
--
--   This is the local statement of stability of the $\mathrm{GL}_3 \times \mathrm{GL}_1$ functional equation under highly ramified twists: for sufficiently ramified $\tau$ the local gamma factor depends only on the central character and on the conductor exponent, and the Whittaker zeta integrals are Laurent polynomials in $N(v)^{-s}$ with uniform abscissae of convergence. It feeds the global functional equation inputs of the cubic-induction argument, being cited by the results that assemble the twisted $L$-functions of a cubic induction datum into a product of root numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_exists_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal MeasureTheory

theorem
LanglandsTunnell.CubicInduction.exists_exists_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h) :
    ∃ c₀ : ℕ, 1 ≤ c₀ ∧
      ∀ (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v τ c →
        ‖(τ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1 →
        c₀ ≤ c →
        (letI := localBorel ℚ v
        ∃ σ₀ σ₁ : ℝ,
          (∀ g : LocalGL3 v,
            ∃ P : ℂ → ℂ,
              (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
                P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
              IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g = P s) ∧
              IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                    W τ (1 - s) g =
                  ((ωv (-1) : ℂˣ) : ℂ) * ((τ (-1) : ℂˣ) : ℂ) *
                    (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ωv * τ) *
                      LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v τ ^ 2 *
                        (Ideal.absNorm v.asIdeal : ℂ) ^ ((3 * (c : ℂ)) * (1 / 2 - s))) * P s)) ∧
        (∃ (g : LocalGL3 v) (s : ℂ), σ₀ < s.re ∧
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g ≠ 0)) := by sorry
