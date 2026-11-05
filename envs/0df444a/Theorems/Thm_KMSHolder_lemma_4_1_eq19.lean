-- Prove2me | Theorems.Thm_KMSHolder_lemma_4_1_eq19
-- name    : KMSHolder.lemma_4_1_eq19
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:55.645496+00:00
-- url     : https://prove2.me/theorems/5a7eb86a-0c87-47bf-8e54-0f7dc8d7231d
-- title:
--   Lemma 4.1 (19): $\Delta^{1/p_n}_{\phi_n,\Omega}\cdots\Delta^{1/p_1}_{\phi_1,\Omega}\Omega = \Delta^{1/2p_n}A_n\Delta^{1/2p_n}\cdots\Delta^{1/2p_1}A_1\Omega$ (corrected: $0 < p_j^{-1}$)
-- statement:
--   Let $M$ be a von Neumann algebra on $H$ with cyclic and separating unit vector $\Omega$ and modular operator $\Delta$. Let $n \ge 1$, let $A_1, \dots, A_n \in M$ be positive, and let $p_1, \dots, p_n$ be real numbers with $0 < p_j^{-1} \le 1/2$ and
--
--   $$
--   \sum_{j=1}^n \frac{1}{p_j} = \frac12 .
--   $$
--
--   Let $\phi_j$ be the positive normal functionals of the first part of Lemma 4.1, with relative modular operators $\Delta_{\phi_j,\Omega}$: $\Delta^{1/p_j}_{\phi_j,\Omega}\Omega = \Delta^{1/2p_j}A_j\Omega$ and $\phi_j(\mathbb 1)^{1/p_j} = \|\Delta^{1/2p_j}A_j\Omega\|_{p_j}$. Then
--
--   $$
--   \Delta^{1/p_n}_{\phi_n,\Omega} \cdots \Delta^{1/p_1}_{\phi_1,\Omega}\,\Omega
--   = \Delta^{1/2p_n} A_n \Delta^{1/2p_n} \cdots \Delta^{1/2p_2} A_2 \Delta^{1/2p_2}\, \Delta^{1/2p_1} A_1 \Omega \in H, \qquad (19)
--   $$
--
--   both sides being iterated compositions in which every intermediate vector lies in the domain of the next operator.
--
--   The identity expresses a product of relative modular powers, which Araki's estimate (8) controls, through the modular operator and the $A_j$; together with Lemma 4.2 it turns the Hölder inequality into an instance of (8).
--
--   **Formalization Note** The families are indexed by $\mathbb N$ with the paper's numbering $j = 1, \dots, n$. The right-hand side is: $A_1\Omega$, then $\Delta^{1/2p_1}$; then for $j = 2, \dots, n$ the block $\Delta^{1/2p_j}$, $A_j$, $\Delta^{1/2p_j}$, as in (27) on p.8.
--
--   Differences from the source:
--   - correction: $0 \le p_j^{-1}$ (inherited from (18)) → $0 < p_j^{-1}$; reason: at $p_j^{-1} = 0$ the functionals $\phi_j$ of (18) need not exist (counterexample in the first part of the lemma: $M = \mathbb C$, $\Omega = 1$, $A = 2$).
--   - reading: "$\equiv$ as elements in $L_2(M,\Omega)^*$" with $H = H^* = L_2(M,\Omega)^*$, "$\in H$" → both iterated compositions exist as vectors of $H$, step by step, and are equal; reason: the lemma asserts the common value is a vector of $H$.
--   - encoding: the $\phi_j$ of the first part → hypotheses: $\phi_j$ positive normal, $T_j$ with `IsRelModular S (φ j) (T j)`, (18) and the norm identity; reason: these are exactly the (unique) $\phi_j$ of the first part.
--   - encoding: KMS standard form; $M^+_*$; indices → `StandardModularData`; `IsPosNormal`; $\mathbb N$-indexed families; reason: Lean convention; same instances.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, Lemma 4.1, eq. (19), p.7; eq. (27), p.8

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_KMSHolder_relIter
import Definitions.Def_KMSHolder_modPowGraph
import Definitions.Def_KMSHolder_PosSpectralCalculus
import Definitions.Def_KMSHolder_posPowGraph
import Definitions.Def_KMSHolder_IsRelModular
import Definitions.Def_KMSHolder_amNorm

open OAI.BoundedRecovery HollandsSanders.CFTBound

namespace KMSHolder

/-- Jäkel–Robl, arXiv:1103.3608v2, Lemma 4.1, eq. (19), p.7: "If also `Σⱼ 1/pⱼ = 1/2` holds,
then `Δ^{1/pₙ}_{φₙ,Ω} ⋯ Δ^{1/p₁}_{φ₁,Ω} Ω = Δ^{1/2pₙ} Aₙ Δ^{1/2pₙ} ⋯ Δ^{1/2p₁} A₁ Ω ∈ H`."

Let `A₁, …, Aₙ ∈ M⁺`, reals `pⱼ` with `0 < pⱼ⁻¹ ≤ 1/2` and `Σⱼ 1/pⱼ = 1/2`, and let `φⱼ`,
`Tⱼ = Δ_{φⱼ,Ω}` be as in the first part of the lemma (18): `Δ^{1/pⱼ}_{φⱼ,Ω} Ω = Δ^{1/2pⱼ} AⱼΩ` and
`φⱼ(1)^{1/pⱼ} = ‖Δ^{1/2pⱼ}AⱼΩ‖_{pⱼ}`. Then both iterated compositions exist as vectors of `H`,
every step lying in the domain of the next operator, and they are equal:
* left: `Ω`, then `Δ^{1/p₁}_{φ₁,Ω}`, `Δ^{1/p₂}_{φ₂,Ω}`, …, `Δ^{1/pₙ}_{φₙ,Ω}`;
* right: `A₁Ω`, then `Δ^{1/2p₁}`; then for `j = 2, …, n` the block `Δ^{1/2pⱼ}`, `Aⱼ`, `Δ^{1/2pⱼ}`
  (the pattern of (19) and of (27), p.8).

**Formalization Note.**
* Indices are the paper's (`j = 1, …, n`), on `ℕ`-indexed families; other indices are unused.
* The paper's "≡ as elements in `L₂(M,Ω)*`" with `H = H* = L₂(M,Ω)*` (p.8) is read as equality of
  vectors of `H` (the lemma says "∈ H").
* `Tⱼ` is any operator with `IsRelModular S (φ j) (T j)` (it is unique); powers of `Tⱼ` follow the
  support convention; `M⁺_*` is `IsPosNormal`; `‖·‖_p` is `amNorm`.
* Correction inherited from (18): `0 < pⱼ⁻¹` in place of `0 ≤ pⱼ⁻¹`; at `pⱼ⁻¹ = 0` the `φⱼ` of
  (18) need not exist (`M = ℂ`, `Ω = 1`, `A = 2`). -/
theorem lemma_4_1_eq19 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StandardModularData H) (n : ℕ) (hn : 1 ≤ n)
    (A : ℕ → H →L[ℂ] H) (hA : ∀ j ∈ Finset.Icc 1 n, A j ∈ S.M ∧ (A j).IsPositive)
    (p : ℕ → ℝ) (hp : ∀ j ∈ Finset.Icc 1 n, 0 < (p j)⁻¹ ∧ (p j)⁻¹ ≤ 1 / 2)
    (hsum : ∑ j ∈ Finset.Icc 1 n, 1 / p j = 1 / 2)
    (φ : ℕ → (H →L[ℂ] H) → ℂ) (T : ℕ → PosSpectralCalculus H)
    (hφ : ∀ j ∈ Finset.Icc 1 n, IsPosNormal (S.M : Set (H →L[ℂ] H)) (φ j) ∧
      IsRelModular S (φ j) (T j) ∧
      ∃ ζ : H, (A j S.xi, ζ) ∈ modPowGraph S ((1 / (2 * p j) : ℝ) : ℂ) ∧
        (S.xi, ζ) ∈ posPowGraph (T j) ((1 / p j : ℝ) : ℂ) ∧
        ENNReal.ofReal ((φ j 1).re ^ (1 / p j)) = amNorm S (p j) ζ) :
    let lhsVecs : Set H :=
      relIter (fun i => posPowGraph (T (i + 1)) ((1 / p (i + 1) : ℝ) : ℂ)) n S.xi
    let rhsSteps : ℕ → Set (H × H) := fun i =>
      {q | ∃ u w : H, (q.1, u) ∈ modPowGraph S ((1 / (2 * p (i + 2)) : ℝ) : ℂ) ∧
        w = A (i + 2) u ∧ (w, q.2) ∈ modPowGraph S ((1 / (2 * p (i + 2)) : ℝ) : ℂ)}
    let rhsVecs : Set H :=
      {y | ∃ x : H, (A 1 S.xi, x) ∈ modPowGraph S ((1 / (2 * p 1) : ℝ) : ℂ) ∧
        y ∈ relIter rhsSteps (n - 1) x}
    lhsVecs.Nonempty ∧ rhsVecs.Nonempty ∧ ∀ x ∈ lhsVecs, ∀ y ∈ rhsVecs, x = y := by sorry

end KMSHolder
