-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero_of_ne_zero_of_principalCongruence_of_two_mul_le
-- name    : LanglandsTunnell.CubicInduction.forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero_of_ne_zero_of_principalCongruence_of_two_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/2bab7723-75e4-537d-a3aa-f97c2770627d
-- title:
--   Stability of the GL₃× GL₁ local functional equation
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$, write $N=\lvert\mathcal{O}/v\rvert$ for the absolute norm of $v$, and let $\psi_v$ be the inverse of the standard additive character $\psi_{\mathbb{Q},v}$ of the completion $\mathbb{Q}_v$. Let $W:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ satisfy: $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for all upper unipotent $u(x,y,z)$ and all $g$; $W\neq 0$; the space of $\psi_v$-Whittaker functionals on the representation of $\mathrm{GL}_3(\mathbb{Q}_v)$ by right translation on the span of the right translates of $W$ has rank at most $1$; every nonzero $F$ in that span has $W$ in the span of its own right translates; some open subgroup $U_v$ fixes $W$ under right translation; for every open subgroup $U_v$ there is a finite set $B$ of functions such that each $U_v$-right-invariant member of the span of the translates of $W$ lies in the $\mathbb{C}$-span of $B$; and $W(t\cdot 1_3\,h)=\omega_v(t)W(h)$ for a character $\omega_v$ of $\mathbb{Q}_v^\times$ with values of absolute value $1$. Let $m\ge 1$ be such that $W(gk)=W(g)$ whenever all entries of $k-1$ and of $k^{-1}-1$ have valuation at most $\exp(-m)$. The assertion is: for every character $\tau$ of $\mathbb{Q}_v^\times$ and every $c\in\mathbb{N}$ such that $\tau$ is trivial on the $c$-th higher unit group while for each $m'<c$ some unit of the $m'$-th higher unit group has $\tau\neq 1$, such that $\lvert\tau(\varpi_v)\rvert=1$ for the chosen uniformizer unit, and such that $2m\le c$, there exist real $\sigma_0,\sigma_1$ with the following properties. For every $g\in\mathrm{GL}_3(\mathbb{Q}_v)$ there is a function $P:\mathbb{C}\to\mathbb{C}$ of the form $P(s)=Q(N^{-s})\,N^{ks}$ for some polynomial $Q$ over $\mathbb{C}$ and some $k\in\mathbb{N}$ such that: for $\operatorname{Re} s>\sigma_0$ the function $a\mapsto W(\iota(\mathrm{diag}(a,1))g)\tau(a)\,\lvert a\rvert^{s-1}$ is integrable for the multiplicative measure on $\mathbb{Q}_v^\times$ obtained by pulling back along $\mathbb{Q}_v^\times\hookrightarrow\mathbb{Q}_v$ the measure $d x/\lvert x\rvert$ built from the self-dual Haar measure, and the corresponding integral `localZeta30` equals $P(s)$ there; for $\operatorname{Re} s>\sigma_1$ the analogous two-variable integrand in $(a,x)$ formed from $g'\mapsto W(w_3\,{}^t g'^{-1})$, the character $\tau^{-1}$, the lower unipotent $n^-(x)$ and the point $w'_3\,{}^tg^{-1}$ is integrable for the product of that multiplicative measure with the self-dual Haar measure; and for $\operatorname{Re}(1-s)>\sigma_1$, $$\widetilde Z(1-s)=\omega_v(-1)\tau(-1)\,\varepsilon(\omega_v\tau)\,\varepsilon(\tau)^2\,N^{3c(1/2-s)}\,P(s),$$ where $\widetilde Z$ is `localZetaDual31`, i.e. the `localZeta31` integral of $g'\mapsto W(w_3\,{}^tg'^{-1})$ against $\tau^{-1}$ at $w'_3\,{}^tg^{-1}$, and $\varepsilon$ denotes the standard root number `stdRootNumberAt` at $v$. Moreover `localZeta30` is nonzero for some $g$ and some $s$ with $\operatorname{Re} s>\sigma_0$.
--
--   This is the stability of the $\mathrm{GL}_3\times\mathrm{GL}_1$ local functional equation under highly ramified twists, in the form of Jacquet–Shalika's lemma on highly ramified $\varepsilon$-factors, with the threshold for the conductor exponent made explicit as $c\ge 2m$ in terms of a principal congruence depth $m$ of the Whittaker function, and with the usual normalisation $W(1)=1$ weakened to $W\neq 0$. It feeds the Rankin–Selberg statement on twisted local functional equations for coefficient functions of principal series of $\mathrm{GL}_3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero_of_ne_zero_of_principalCongruence_of_two_mul_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero_of_ne_zero_of_principalCongruence_of_two_mul_le
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hne : W ≠ 0)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)

    (m : ℕ) (hm : 1 ≤ m)
    (hWm : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      (∀ i j : Fin 3, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∀ (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v τ c →
        ‖(τ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1 →
        2 * m ≤ c →
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
