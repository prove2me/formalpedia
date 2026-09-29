-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference
-- name    : LanglandsTunnell.CubicInduction.integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/7dac403e-ea28-5475-a506-641b3e00c780
-- title:
--   Integrability of local zeta integrands killed by three twisted differences
-- statement:
--   Fix a nonzero prime $v$ of the ring of integers of $\mathbb{Q}$, and work on the completion $\mathbb{Q}_v$ with its Borel $\sigma$-algebra. Let $\beta : \mathrm{Fin}\,3 \to \mathbb{C}$, and let $D$ be an operator assigned to each scalar and each function $f : \mathbb{Q}_v \to \mathbb{C}$ which, by hypothesis `hD`, is the twisted difference $D_\alpha f(a) = f(a) - \alpha f(a/\varpi)$, where $\varpi$ is the uniformiser unit [`NumberField.AdelicLevel.uniformizerUnit`](def/NumberField_AdelicLevel.html#L788) at $v$. Let $\phi : \mathbb{Q}_v \to \mathbb{C}$ satisfy: for each $t \neq 0$, $\phi$ is constantly $\phi(t)$ on a neighbourhood of $t$; there is a real $B$ with $\phi(t) = 0$ whenever $B < |t|_v$ (the value of `modulus`, equal to $\|t\|$ by [`LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`](thm.html#LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm)); and $D_{\beta_0} D_{\beta_1} D_{\beta_2} \phi$ vanishes on a neighbourhood of $0$. Let $\chi : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be a locally constant homomorphism and $s \in \mathbb{C}$ with $\|\beta_i\| \cdot \|\chi(\varpi)\| \cdot (\mathrm{absNorm}\, v)^{-\mathrm{Re}\,s} < 1$ for each $i$. Then $x \mapsto \phi(x)\,\chi(x)\,|x|_v^{s}$ (with $\chi$, $|\cdot|_v$ extended by $0$ at $0$) is integrable for `mulMeasure (selfDualHaarAt ℚ v)`, i.e. the self-dual additive Haar measure at $v$ restricted to $\mathbb{Q}_v \setminus \{0\}$ and given density $|x|_v^{-1}$.
--
--   This is the absolute-convergence input for Tate's local zeta integrals in the half-plane determined by the three roots $\beta_i$: the cubic twisted-difference relation near $0$ replaces the usual Schwartz–Bruhat hypothesis and allows the integral over the shells to be summed as a geometric series. It is used in the analysis of local zeta integrals attached to Whittaker functions of cubic type, notably in establishing their convergence and Laurent expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem
LanglandsTunnell.CubicInduction.integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference
    (v : HeightOneSpectrum (𝓞 ℚ)) (β : Fin 3 → ℂ)
    (D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ)
    (hD : ∀ (α : ℂ) (f : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ),
      D α f a = f a - α * f (a / (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ)))
    (φ : v.adicCompletion ℚ → ℂ) (hφ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, φ t' = φ t)
    (hφB : ∃ B : ℝ, ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → φ t = 0)
    (hrec : ∀ᶠ x in nhds (0 : v.adicCompletion ℚ), D (β 0) (D (β 1) (D (β 2) φ)) x = 0)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (s : ℂ)
    (hs : ∀ i, ‖β i‖ * ‖(χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ *
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    Integrable (fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v)) := by sorry
