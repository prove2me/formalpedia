-- Prove2me | Theorems.Thm_GaussDiffSVP_theorem_4_3
-- name    : GaussDiffSVP.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:32.903654+00:00
-- url     : https://prove2.me/theorems/266e298a-b51f-407f-a8d0-e2148404ab0e
-- title:
--   Theorem 4.3 — full differencing: parent in $\mathcal C(\nu', D+\eta+\log(1+\rho))$
-- statement:
--   A parent draws a local shift $d$; given $d$ its two children are independent, with the left child in $\mathcal C(\nu_{L,d},\varepsilon_L)$ and the right child in $\mathcal C(\nu_{R,d},\varepsilon_R)$, $\varepsilon_L,\varepsilon_R$ uniform over $d$, and they are fully merged with pairwise independent coins of marginals $q_d$. Put $D = \varepsilon_L+\varepsilon_R$,
--   $$\lambda_d = \Phi_{q_d}(\nu_{L,d},\nu_{R,d}),\quad Q_{L,d} = \Psi_{q_d}(\Delta_*\nu_{L,d},\nu_{R,d}^{\otimes2}),\quad Q_{R,d} = \Psi_{q_d}(\nu_{L,d}^{\otimes2},\Delta_*\nu_{R,d}).$$
--   If for a reference $\nu'$ and numbers $\eta,\rho\ge0$
--   $$e^{-\eta}\nu'\le\mathbb E_d[\lambda_d]\le e^{\eta}\nu',\qquad \mathbb E_d[\lambda_d^{\otimes2}+Q_{L,d}+Q_{R,d}]\le e^{\eta}(1+\rho)(\nu')^{\otimes2},$$
--   then the full output lies in $\mathcal C(\nu', D+\eta+\log(1+\rho))$. It separates the counting argument from the geometry of a particular kernel.
--
--   Differences from the source:
--   - generalization: $d$ uniform on $(\Gamma/2)/\Gamma$ → $d$ drawn from an arbitrary law $\omega$ on an arbitrary type; reason: the proof only averages over $d$; the uniform half-grid law is an instance
--   - encoding: bounds conditional on $\mathcal H_a$ and $\mathcal A_a$ → laws and numbers given $\mathcal H_a$; the parent law is the $\omega$-mixture of the merge laws; reason: the statement for every value of $\mathcal H_a$
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 4.3, p.24 ((25)–(26), p.24)

import Mathlib
import Definitions.Def_GaussDiffSVP_InClassC
import Definitions.Def_GaussDiffSVP_transport1
import Definitions.Def_GaussDiffSVP_transport2
import Definitions.Def_GaussDiffSVP_diagM
import Definitions.Def_GaussDiffSVP_IsCoinKernel
import Definitions.Def_GaussDiffSVP_fullMergeLaw

open scoped ENNReal

namespace GaussDiffSVP

/-- Theorem 4.3 (Full differencing) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.24). A parent draws its local shift `d` from the law
`ω`; given `d`, its two children are independent, the left child lies in `C(ν_{L,d}, ε_L)` and the
right child in `C(ν_{R,d}, ε_R)` with `ε_L, ε_R` uniform over `d`, and they are fully merged with
pair map `T` and pairwise independent coins of marginals `q_d`. Put `D = ε_L + ε_R`,
`λ_d = Φ_{q_d}(ν_{L,d}, ν_{R,d})` (25), `Q_{L,d} = Ψ_{q_d}(Δ_*ν_{L,d}, ν_{R,d}^{⊗2})` and
`Q_{R,d} = Ψ_{q_d}(ν_{L,d}^{⊗2}, Δ_*ν_{R,d})` (26). If, for a reference `ν′` and `η, ρ ≥ 0`,
`e^{−η}ν′ ≤ E_d[λ_d] ≤ e^{η}ν′` (27) and `E_d[λ_d^{⊗2} + Q_{L,d} + Q_{R,d}] ≤ e^{η}(1 + ρ)(ν′)^{⊗2}`
(28), then the parent output lies in `C(ν′, D + η + log(1 + ρ))` (29).

**Formalization Note.** The retained information `H_a` is fixed: all laws, references and numbers
are those given `H_a`, and the statement holds for each of its values. `E_d` is the average
under the shift law `ω`, which is arbitrary (the uniform law on `(Γ/2)/Γ` is the paper's
instance); the parent law is the `ω`-mixture of the merge laws. -/
theorem theorem_4_3 {α β γ D : Type*} (ω : PMF D) (μL : D → PMF (List α))
    (μR : D → PMF (List β)) (T : α → β → γ) (q : D → α → β → ℝ≥0∞)
    (κ : D → (lL : List α) → (lR : List β) → PMF (Fin lL.length × Fin lR.length → Bool))
    (hκ : ∀ d, IsCoinKernel (q d) (κ d))
    (νL : D → α → ℝ≥0∞) (νR : D → β → ℝ≥0∞) (εL εR : ℝ)
    (hL : ∀ d, InClassC (μL d) (νL d) εL) (hR : ∀ d, InClassC (μR d) (νR d) εR)
    (ν' : γ → ℝ≥0∞) (η ρ : ℝ) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (h27 : ∀ z, ENNReal.ofReal (Real.exp (-η)) * ν' z ≤
        ∑' d, ω d * transport1 T (q d) (νL d) (νR d) z ∧
      ∑' d, ω d * transport1 T (q d) (νL d) (νR d) z ≤ ENNReal.ofReal (Real.exp η) * ν' z)
    (h28 : ∀ z z', ∑' d, ω d * (transport1 T (q d) (νL d) (νR d) z *
          transport1 T (q d) (νL d) (νR d) z' +
        transport2 T (q d) (diagM (νL d)) (fun y y' => νR d y * νR d y') z z' +
        transport2 T (q d) (fun x x' => νL d x * νL d x') (diagM (νR d)) z z') ≤
      ENNReal.ofReal (Real.exp η * (1 + ρ)) * (ν' z * ν' z')) :
    InClassC (ω.bind fun d => fullMergeLaw (μL d) (μR d) T (κ d)) ν'
      (εL + εR + η + Real.log (1 + ρ)) := by sorry

end GaussDiffSVP
