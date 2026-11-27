-- Prove2me | Theorems.Thm_HorodeckiBoundKey_Supplement_key_le_regularized_ree
-- name    : HorodeckiBoundKey.Supplement.key_le_regularized_ree
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:18:59.153899+00:00
-- url     : https://prove2.me/theorems/645cc57f-e8bb-589f-b762-1e4d753d1457
-- title:
--   Theorem 2 (corrected: relative entropy in bits, as the key) — distillable key is at most the regularized relative entropy of entanglement, $K_D(\rho_{AB})\le E_r^\infty(\rho_{AB})$
-- statement:
--   Let $\rho_{AB}$ be a state (a positive semidefinite matrix of trace one) on $\mathbb C^a\otimes\mathbb C^b$, where Alice holds $A=\mathbb C^a$ and Bob holds $B=\mathbb C^b$. Write $K_D(\rho)$ for its distillable key, $S(\rho\|\sigma)=\mathrm{Tr}[\rho(\log\rho-\log\sigma)]$ for the relative entropy ($+\infty$ when the support of $\rho$ is not contained in that of $\sigma$), and
--   $$
--   E_r(\rho) = \inf_{\sigma\ \text{separable}} S(\rho\|\sigma),\qquad
--   E_r^\infty(\rho) = \lim_{n\to\infty}\frac{E_r(\rho^{\otimes n})}{n}
--   $$
--   for the relative entropy of entanglement and its regularization, where in $\rho^{\otimes n}$ Alice holds all $n$ copies of $A$ and Bob all $n$ copies of $B$. Then
--   $$
--   K_D(\rho_{AB}) \le E_r^\infty(\rho_{AB}).
--   $$
--
--   This is the general upper bound on distillable key of the paper (Theorem 2, p.4); the paper refers to its ref. [18] for the proof. Since $E_r=0$ on separable states, it implies that separable states carry no key, and since $E_r^\infty$ can be strictly smaller than the entanglement cost $E_c$ (for the antisymmetric Werner state, $E_r^\infty=\log\frac{d+2}{d}$ while $E_c=1$), it shows that the key rate can be strictly below the entanglement cost. Together with the main result it gives the chain $E_D\le K_D\le E_r^\infty\le E_c$ of the paper's summary.
--
--   **Formalization Note** $K_D$ is the operational private-dit rate `Gap48.P42.distillableKey` (key counted in bits, valued in $[0,\infty]$), the same rate the published goal `HorodeckiBoundKey.main_result` uses. $E_r^\infty$ is the published `Dependency50.P24.regularizedREE`: the infimum over $n\ge1$ of $E_r(\rho^{\otimes n})/n$, with $E_r$ the infimum over finite convex combinations of product states (`Information100.P54.relativeEntanglement`) and the relative entropy in bits. The instances `[NeZero a] [NeZero b]` only provide the nonempty registers the definitions require; no state lives on an empty register.
--
--   Differences from the source:
--   - reading: distillable key K_D (key drawn by local operations and public communication; not defined formally in the paper) → K_γ, the operational private-dit rate Gap48.P42.distillableKey under deterministic finite adaptive LOCC (ℝ≥0∞); reason: p.2 identifies the two rates ("We thus have equality of the two rates", with "Clearly K_γ ≤ K_D"); the published goal and separable_no_key use this one key rate
--   - correction: S(ρ‖σ) := Tr[ρ(ln ρ − ln σ)] in nats (p.4) → relative entropy in bits (log₂), so E_r and E_r^∞ in bits; reason: the key rate counts bits, and in nats the bound is false: a singlet has K_D = 1 bit while E_r^∞ = ln 2 ≈ 0.69 nats; the paper itself uses bits on p.4 (E_r^∞(ϱ_a) = log((d+2)/d) beside E_c(ϱ_a) = 1)
--   - encoding: E_r^∞(ρ) := lim_{n→∞} E_r(ρ^{⊗n})/n → the infimum over n ≥ 1 of E_r(ρ^{⊗n})/n (Dependency50.P24.regularizedREE); reason: E_r is subadditive under tensor products, so by Fekete's lemma the limit exists and equals this infimum; same value for every state
--   - encoding: separable states (sep) → finite convex combinations of product density matrices (IsSeparableDensity); reason: in finite dimensions the convex hull of product states is closed (Carathéodory), so the infimum is over the same set
--   - encoding: a bipartite state on finite-dimensional A, B; real-valued rates → ρ on Fin a × Fin b with [NeZero a] [NeZero b], rates in ℝ≥0∞; reason: no density matrix exists on an empty register, and ℝ≥0∞ avoids the junk value of a real supremum or infimum; same instances
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, Theorem 2, p.4 (with the definition of E_r, pp.3–4, and of K_D, K_γ, p.2)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

open QAlgorithms QAlgorithms.Papers.Independent
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (regularizedREE)
open QAlgorithms.Papers.Independent.Gap48.P42 (distillableKey)

namespace HorodeckiBoundKey.Supplement

/-- Horodecki, Horodecki, Horodecki, Oppenheim, *Secure key from bound entanglement*,
arXiv:quant-ph/0309110v2, Theorem 2, p.4: "K_D(ρ_AB) ≤ E_r^∞(ρ_AB). where E_r^∞ is the
regularization of the relative entropy of entanglement E_r^∞(ρ) := lim_{n→∞} E_r(ρ^{⊗n})/n",
with `E_r(ρ) := inf_{σ ∈ sep} S(ρ‖σ)` (pp.3–4). The paper defers the proof to its ref. [18].

For every state `ρ` of a finite bipartite system, Alice `Fin a`, Bob `Fin b`, the distillable
key is at most the regularized relative entropy of entanglement across the same cut.

**Formalization Note.** `K_D` is read as `K_γ` (p.2: "We thus have equality of the two
rates"), the operational private-dit rate `Gap48.P42.distillableKey` (key in bits, `ℝ≥0∞`),
as in the published goal and `separable_no_key`. `E_r^∞` is the published
`Dependency50.P24.regularizedREE`: the infimum over `n ≥ 1` of `E_r(ρ^{⊗n})/n`, where the
`n` copies keep every `A` factor with Alice and every `B` factor with Bob, `E_r` is the infimum
over finite convex combinations of product states, and the relative entropy is measured in
bits (`log₂`, `+∞` off support); the printed limit exists and equals this infimum by
subadditivity of `E_r` (Fekete). The relative entropy on p.4 is written with `ln`; bits are
used because the key is counted in bits (a singlet has 1 bit of key and `E_r = ln 2` nats).
`[NeZero a] [NeZero b]` only supply the nonemptiness the definitions need; a density matrix
on an empty index type does not exist. -/
theorem key_le_regularized_ree {a b : ℕ} [NeZero a] [NeZero b]
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hρ : IsDensityMatrix ρ) :
    distillableKey ρ ≤ regularizedREE ρ := by sorry

end HorodeckiBoundKey.Supplement
