-- Prove2me | Theorems.Thm_KMSHolder_lemma_4_2
-- name    : KMSHolder.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:02.548209+00:00
-- url     : https://prove2.me/theorems/ab7e2cb4-4b04-43d6-ba00-0a4dba355108
-- title:
--   Lemma 4.2 (28): $\|\Delta^{1/2p}A\Omega\|_p = \phi(\mathbb 1)^{1/p} = \omega(A\Delta^{1/p}A\cdots\Delta^{1/p}A)^{1/p}$
-- statement:
--   Let $M$ be a von Neumann algebra on $H$ with cyclic and separating unit vector $\Omega$, vector state $\omega$ and modular operator $\Delta$. Let $p \ge 2$ be an even integer and $A \in M$ positive. Then there is a positive normal functional $\phi$ on $M$ such that
--
--   $$
--   \|\Delta^{1/2p}A\Omega\|_p = \phi(\mathbb 1)^{1/p}
--   \qquad\text{and}\qquad
--   \phi(\mathbb 1) = \omega\big(A\Delta^{1/p}A \cdots \Delta^{1/p}A\big), \qquad (28)
--   $$
--
--   where the right-hand side, with $p$ copies of $A$ and $p - 1$ powers $\Delta^{1/p}$, is Araki's multiple-time correlation: the value at $(1/p, \dots, 1/p)$ of the analytic continuation of $s \mapsto \langle\Omega, A\Delta^{is_{p-1}}A\cdots A\Delta^{is_1}A\Omega\rangle$. In particular $\|\Delta^{1/2p}A\Omega\|_p = |||A|||_p$, the quantity on the right of the Hölder inequality.
--
--   **Formalization Note** $\|\cdot\|_p$ is `amNorm` (valued in $[0,\infty]$, identity stated through `ENNReal.ofReal`). The continuation value is stated for every continuation $G$ (it is unique).
--
--   Differences from the source:
--   - generalization: the KMS state $\omega_\beta$ → any von Neumann algebra with cyclic separating unit vector, $\Delta$ its modular operator; reason: a KMS state's GNS data are an instance ($\Delta = e^{-\beta L}$, pp.2, 4).
--   - reading: $\phi(\mathbb 1)^{1/p} = \omega_\beta(A\Delta^{1/p}A\cdots\Delta^{1/p}A)^{1/p}$ → $\phi(\mathbb 1) = G(1/p, \dots, 1/p)$; reason: the $p$-th root of the right-hand side is defined only once the value is a nonnegative real, which is what the identity of values says.
--   - reading: Araki's symbolic notation → every continuation $G$ with `IsArakiContinuation`; reason: the continuation exists and is unique (milestone `KMSHolder.araki_continuation_exists_unique`).
--   - encoding: $p \in \mathbb N$ even → `Even p` and `2 ≤ p`; $\|\cdot\|_p$ → `amNorm`; $M^+_*$ → `IsPosNormal`; reason: $p = 0$ has no $1/p$; Lean convention otherwise.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, Lemma 4.2, eq. (28), p.8

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_KMSHolder_modPowGraph
import Definitions.Def_KMSHolder_amNorm
import Definitions.Def_KMSHolder_IsArakiContinuation

open OAI.BoundedRecovery HollandsSanders.CFTBound

namespace KMSHolder

/-- Jäkel–Robl, arXiv:1103.3608v2, Lemma 4.2, eq. (28), p.8: "Let `p ∈ ℕ` be even and `A ∈ M⁺`.
Then there exists `φ ∈ M⁺_*` such that
`‖Δ^{1/2p}AΩ‖_p = φ(1)^{1/p} = ω_β(A Δ^{1/p} A ⋯ Δ^{1/p} A)^{1/p}`. (28)
On the r.h.s. we have used Araki's symbolic notation introduced in the sentence following
Equ. (2)."

For even `p ≥ 2` and `A ∈ M⁺` there is a positive normal functional `φ` with
1. `‖Δ^{1/2p}AΩ‖_p = φ(1)^{1/p}` (`AΩ` in the domain of `Δ^{1/2p}`, `‖·‖_p = amNorm`);
2. `φ(1) = ω(A Δ^{1/p} A ⋯ Δ^{1/p} A)` (`p` copies of `A`), i.e. `φ(1)` is the value at
   `(1/p, …, 1/p)` of every analytic continuation `G` of the chain of `p` copies of `A`.

**Formalization Note.**
* Reading: the page equates `p`-th roots; the value itself is stated equal to `φ(1)`, a
  nonnegative real, which is the reading under which the root of the right-hand side is defined.
* `p ≥ 2` encodes "`p` even" with `1/p` meaningful (`p = 0` excluded).
* The chain of `p` copies of `A` has `p − 1` complex variables (`Fin (p - 1 + 1)` copies);
  `(1/p, …, 1/p)` lies in `I⁽ᵖ⁻¹⁾`. Standard modular data replace the KMS state. -/
theorem lemma_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StandardModularData H) (p : ℕ) (hp_even : Even p) (hp2 : 2 ≤ p)
    (A : H →L[ℂ] H) (hA : A ∈ S.M) (hApos : A.IsPositive) :
    ∃ φ : (H →L[ℂ] H) → ℂ, IsPosNormal (S.M : Set (H →L[ℂ] H)) φ ∧
      (∃ ζ : H, (A S.xi, ζ) ∈ modPowGraph S ((1 / (2 * (p : ℝ)) : ℝ) : ℂ) ∧
        amNorm S p ζ = ENNReal.ofReal ((φ 1).re ^ (1 / (p : ℝ)))) ∧
      ∀ G : (Fin (p - 1) → ℂ) → ℂ,
        IsArakiContinuation S (fun _ : Fin (p - 1 + 1) => A) G →
          G (fun _ => ((1 / (p : ℝ) : ℝ) : ℂ)) = φ 1 := by sorry

end KMSHolder
