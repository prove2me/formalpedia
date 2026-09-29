-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_localZetaDual31_eq_mul_localZeta30_of_isGL3PsiWhittakerFn_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.exists_forall_localZetaDual31_eq_mul_localZeta30_of_isGL3PsiWhittakerFn_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/98716bd4-9583-5827-9b22-1c8c64c6386c
-- title:
--   Stability of the GL₃timesGL₁ local functional equation under ramified twists
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, and let $\psi_v$ be the inverse of the standard additive character $\psi_{\mathbb{Q},v}$ of $\mathbb{Q}_v$. Let $W:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ satisfy: $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x,y,z$; $W(1)=1$; the space of $\psi_v$-Whittaker functionals on the span of the right translates of $W$, viewed as a representation by right translation, has $\mathbb{C}$-rank at most $1$; every nonzero $F$ in that span has $W$ in the span of its own right translates; $W$ is right invariant under some open subgroup; and for every open subgroup $U_v$ there is a finite set $B$ of functions whose $\mathbb{C}$-span contains all right $U_v$-invariant members of the span of the translates of $W$. Let $\omega_v:\mathbb{Q}_v^\times\to\mathbb{C}^\times$ have absolute value $1$ everywhere and satisfy $W(t\cdot I_3\,h)=\omega_v(t)W(h)$. Then there is $c_0\ge 1$ such that for every character $\tau$ of $\mathbb{Q}_v^\times$ with conductor exponent exactly $c$ (trivial on the $c$-th higher unit group, nontrivial on the $m$-th for each $m<c$), with $|\tau(\varpi_v)|=1$ at the chosen uniformizer unit, and with $c\ge c_0$, the following hold, the multiplicative measure $\mu$ on $\mathbb{Q}_v^\times$ being obtained from $d x/|x|$ for the self-dual Haar measure $\nu$ of $\mathbb{Q}_v$, and $\mathbb{Q}_v$ carrying its Borel $\sigma$-algebra. First, for every $g$ there are $P:\mathbb{C}\to\mathbb{C}$ and $\sigma_0,\sigma_1\in\mathbb{R}$ with: $P(s)=Q(N(v)^{-s})\,N(v)^{ms}$ for some $Q\in\mathbb{C}[X]$ and $m\in\mathbb{N}$; the integrand $a\mapsto W(\iota(\mathrm{diag}(a,1))g)\tau(a)|a|^{s-1}$ is $\mu$-integrable for $\mathrm{Re}\,s>\sigma_0$, and there $\int$ of it equals $P(s)$; the corresponding two-variable integrand in $(a,x)$ built from $g'\mapsto W(w_3\,{}^t g'^{-1})$, the character $\tau^{-1}$ and the point $w'\,{}^tg^{-1}$ is $\mu\otimes\nu$-integrable for $\mathrm{Re}\,s>\sigma_1$ ($w_3$ the long Weyl element, $w'$ the transposition of the last two coordinates); and for all $s$ with $\sigma_1<\mathrm{Re}(1-s)$ the dual integral satisfies $$Z^{\sim}(1-s,W,\tau;g)=\omega_v(-1)\tau(-1)\,\varepsilon(\omega_v\tau)\,\varepsilon(\tau)^2\,N(v)^{3c(1/2-s)}P(s),$$ where $\varepsilon(\cdot)$ denotes the standard local root number at $v$ (the standard local $\varepsilon$-factor at $s=1/2$). Secondly, there exist $g$ and $\sigma$ such that the first integral converges for $\mathrm{Re}\,s>\sigma$ and is nonzero at some such $s$.
--
--   This is the stability, under sufficiently ramified twists, of the local functional equation of the $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integrals of a single Whittaker function, with the twisted $\gamma$-factor expressed through the standard root numbers $\varepsilon(\omega_v\tau)\varepsilon(\tau)^2$ and a power of $N(v)$ depending only on the conductor exponent. It feeds the cubic induction step, where the local functional equations at all places are assembled into the global functional equation with its product of root numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_localZetaDual31_eq_mul_localZeta30_of_isGL3PsiWhittakerFn_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal MeasureTheory

theorem
LanglandsTunnell.CubicInduction.exists_forall_localZetaDual31_eq_mul_localZeta30_of_isGL3PsiWhittakerFn_of_norm_eq_one
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
        (∀ g : LocalGL3 v,
          ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
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
        (∃ (g : LocalGL3 v) (σ : ℝ),
          IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ g σ ∧
          ∃ s : ℂ, σ < s.re ∧
            localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g ≠ 0)) := by sorry
