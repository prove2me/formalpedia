-- Prove2me | Theorems.Thm_KMSHolder_lemma_4_1_eq18
-- name    : KMSHolder.lemma_4_1_eq18
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:55.658671+00:00
-- url     : https://prove2.me/theorems/353d8b77-2a41-4a8f-b8be-40e0e2ccbc83
-- title:
--   Lemma 4.1 (18): $\Delta^{1/2p}A\Omega = \Delta^{1/p}_{\phi,\Omega}\Omega$ for a unique $\phi \in M^+_*$ (corrected: $0 < p^{-1}$)
-- statement:
--   Let $M$ be a von Neumann algebra on $H$ with cyclic and separating unit vector $\Omega$ and modular operator $\Delta$. Let $p$ be a real number with
--
--   $$
--   0 < p^{-1} \le \tfrac12,
--   $$
--
--   and let $A \in M$ be positive. Then $A\Omega$ lies in the domain of $\Delta^{1/2p}$, the vector $\zeta = \Delta^{1/2p}A\Omega$ lies in the Araki–Masuda space $L_p(M,\Omega)$, and there is a positive normal functional $\phi$ on $M$ with
--
--   $$
--   \Delta^{1/p}_{\phi,\Omega}\,\Omega = \Delta^{1/2p} A\Omega \qquad (18)
--   \qquad\text{and}\qquad
--   \phi(\mathbb 1)^{1/p} = \|\Delta^{1/2p}A\Omega\|_p .
--   $$
--
--   This $\phi$ is unique: any positive normal functional with both properties agrees with $\phi$ on $M$.
--
--   The lemma converts the vector $\Delta^{1/2p}A\Omega$, which appears in the multiple-time correlation, into the $1/p$-th power of a relative modular operator, so that Araki's estimate (8) applies; it is the first step of the proof of the Hölder inequality for KMS states.
--
--   **Formalization Note** $\Delta^{1/p}_{\phi,\Omega}$ is the $1/p$ power (support convention) of an operator $T$ with `IsRelModular S φ T`, whose existence is asserted, so the uniqueness of $\phi$ is not vacuous. $\|\cdot\|_p$ is `amNorm`, valued in $[0,\infty]$; membership in $L_p$ is `amNorm S p ζ < ⊤`, and the norm identity is stated through `ENNReal.ofReal`.
--
--   Differences from the source:
--   - correction: $0 \le p_j^{-1} \le 1/2$ → $0 < p^{-1} \le 1/2$; reason: at $p^{-1} = 0$ the lemma is false: for $M = \mathbb C$ on $H = \mathbb C$, $\Omega = 1$, $A = 2$, every $\phi \in M^+_*$ is $c\,\omega$ with $c \ge 0$, so $\Delta^0_{\phi,\Omega}\Omega \in \{0, 1\} \ne 2 = A\Omega$, and $\phi(\mathbb 1)^0 = 1 \ne 2 = \|A\Omega\|_\infty$; the paper uses the lemma only for even $p_j \ge 2$.
--   - encoding: $A_1, \dots, A_n$ and $p_1, \dots, p_n$ with unique $\phi_j$ → one $A$ and one $p$; reason: each $\phi_j$ depends only on $A_j$ and $p_j$, so the $n$-fold statement is the conjunction over $j$.
--   - reading: "$\phi_j(\mathbb 1)^{1/p_j} = \|\Delta^{1/2p_j}A_j\Omega\|_{p_j}$" → $\zeta = \Delta^{1/2p}A\Omega$ exists, lies in $L_p(M,\Omega)$, and the identity holds; reason: the $p$-norm of $\zeta$ is presupposed finite.
--   - encoding: $M$ from a KMS state with $\Delta^{1/2} = e^{-\beta L/2}$; $\Delta_{\phi,\Omega}$; $M^+_*$; $\|\cdot\|_p$; uniqueness → `StandardModularData`; `IsRelModular` with the support convention; `IsPosNormal`; `amNorm` in `ℝ≥0∞`; equality of values on $M$; reason: Lean convention; same instances.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, Lemma 4.1, eq. (18), p.7

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_KMSHolder_modPowGraph
import Definitions.Def_KMSHolder_PosSpectralCalculus
import Definitions.Def_KMSHolder_posPowGraph
import Definitions.Def_KMSHolder_IsRelModular
import Definitions.Def_KMSHolder_amNorm

open OAI.BoundedRecovery HollandsSanders.CFTBound
open scoped ENNReal

namespace KMSHolder

/-- Jäkel–Robl, arXiv:1103.3608v2, Lemma 4.1, eq. (18), p.7 (corrected: `0 < p⁻¹`):
"Let `A₁, …, Aₙ ∈ M⁺`. Then there exist unique `φⱼ ∈ M⁺_*` such that for `0 ≤ pⱼ⁻¹ ≤ 1/2`
`Δ^{1/pⱼ}_{φⱼ,Ω} Ω = Δ^{1/2pⱼ} Aⱼ Ω` (18) and `φⱼ(1)^{1/pⱼ} = ‖Δ^{1/2pⱼ}AⱼΩ‖_{pⱼ}`."

Stated for one `A ∈ M⁺` and one real `p` with `0 < p⁻¹ ≤ 1/2` (the `n`-fold statement is the
conjunction over `j`): `AΩ` lies in the domain of `Δ^{1/2p}`; `ζ = Δ^{1/2p}AΩ` lies in
`L_p(M, Ω)` (`amNorm S p ζ < ⊤`); and there is a positive normal functional `φ` with
`Δ^{1/p}_{φ,Ω} Ω = ζ` and `φ(1)^{1/p} = ‖ζ‖_p`, unique (as a functional on `M`) among positive
normal functionals with these two properties.

**Formalization Note.**
* Correction: the page allows `p⁻¹ = 0`; there (18) fails (`M = ℂ` on `H = ℂ`, `Ω = 1`, `A = 2`:
  every `φ ∈ M⁺_*` is `cω`, so `Δ^0_{φ,Ω}Ω ∈ {0, 1} ≠ 2`), and the proof uses the lemma only for
  even `pⱼ ≥ 2`.
* `Δ^{1/p}_{φ,Ω}` is the `1/p` power (support convention) of some `T` with `IsRelModular S φ T`;
  existence of `T` is asserted (`∃ T`), so uniqueness of `φ` is not vacuous.
* `‖·‖_p` is `amNorm`; the norm equation is stated in `ℝ≥0∞` via `ENNReal.ofReal`.
* Standard modular data replace the KMS state; `Δ^{1/2p}` is `modPowGraph S (1/(2p))`. -/
theorem lemma_4_1_eq18 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StandardModularData H) (p : ℝ) (hp_pos : 0 < p⁻¹)
    (hp_le : p⁻¹ ≤ 1 / 2) (A : H →L[ℂ] H) (hA : A ∈ S.M) (hApos : A.IsPositive) :
    ∃ ζ : H, (A S.xi, ζ) ∈ modPowGraph S ((1 / (2 * p) : ℝ) : ℂ) ∧ amNorm S p ζ < ⊤ ∧
      ∃ φ : (H →L[ℂ] H) → ℂ, IsPosNormal (S.M : Set (H →L[ℂ] H)) φ ∧
        (∃ T : PosSpectralCalculus H, IsRelModular S φ T ∧
          (S.xi, ζ) ∈ posPowGraph T ((1 / p : ℝ) : ℂ)) ∧
        ENNReal.ofReal ((φ 1).re ^ (1 / p)) = amNorm S p ζ ∧
        ∀ ψ : (H →L[ℂ] H) → ℂ, IsPosNormal (S.M : Set (H →L[ℂ] H)) ψ →
          (∃ T : PosSpectralCalculus H, IsRelModular S ψ T ∧
            (S.xi, ζ) ∈ posPowGraph T ((1 / p : ℝ) : ℂ)) →
          ENNReal.ofReal ((ψ 1).re ^ (1 / p)) = amNorm S p ζ →
          ∀ a ∈ S.M, ψ a = φ a := by sorry

end KMSHolder
