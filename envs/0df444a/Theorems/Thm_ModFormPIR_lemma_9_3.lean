-- Prove2me | Theorems.Thm_ModFormPIR_lemma_9_3
-- name    : ModFormPIR.lemma_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:03.695182+00:00
-- url     : https://prove2.me/theorems/1c826b69-f8b7-4d98-a162-43f8995b0ad0
-- title:
--   Lemma 9.3, p.34 — transfer of a symmetric expansion from $\mathbb Q(\zeta_q)$ to $\mathbb F_p$
-- statement:
--   Assume there is a symmetric quadratic-phase delta expansion over $\mathbb Q(\zeta_q)$ with support $\mathcal W\times\mathcal A$. Then there is a positive integer $M\le M_d$, where $M_d=D!\cdot q^{dD}$ with $D=q^2(d+1)^q$, such that for every prime $p\equiv1\pmod q$ with $p>M$ and every primitive $q$-th root of unity $\gamma\in\mathbb F_p$ there is a symmetric quadratic-phase delta expansion over $\mathbb F_p$ supported on $\mathcal W\times\mathcal A$. Moreover, given $p$, $\gamma$ and the list of types of the vectors in $\mathcal W$, the coefficients of such an expansion can be computed in $\mathrm{poly}(d,\log p)$ time.
--
--   This is how expansions from Part II, which live in characteristic zero, reach the schemes of Part I, which need a finite field.
--
--   **Formalization Note** $q$ is fixed, so one program serves all $d$, $p$, $\mathcal W$, $\mathcal A$. Its output is decoded by type and by $t$.
--
--   Differences from the source:
--   - reading: "given p, γ, and the list of types of the vectors in 𝒲", for any 𝒲 → this clause assumes 𝒲 permutation-invariant; reason: Lemma 9.1, which defines "symmetric", has this assumption and the proof’s unknowns are indexed by types of 𝒲; a list of types cannot determine a non-invariant 𝒲
--   - reading: "computed in poly(d, log p) time" → an accepting run within C·(d + log₂ p + 1)^e machine steps, word width enough to address poly(d, log p) cells; reason: the source names no machine
--   - encoding: ℚ(ζ_q) → `CyclotomicField q ℚ` with any primitive root ζ; reason: all primitive roots are Galois conjugate
--   - encoding: integer d → 1 ≤ d; reason: the paper’s convention for dimension
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 9.3, p.34 (PDF p.38)

import Mathlib
import Definitions.Def_ModFormPIR_Layouts

set_option autoImplicit false

namespace ModFormPIR

/-- **Lemma 9.3**, p.34. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
A symmetric quadratic-phase delta expansion over `ℚ(ζ_q)` with support `𝒲 × 𝒜` transfers to `𝔽_p`, for every prime `p ≡ 1 (mod q)`
with `p > M` and every primitive `q`-th root `γ ∈ 𝔽_p`; here `0 < M ≤ M_d`. The coefficients are computable from `p, γ` and the list of types in
`poly(d, log p)` time.

**Formalization Note.** `q` is fixed, so `P, b, C, e` depend on `q` only. Time is steps on the machine, and the word need only
address `poly(d, log p)` cells. The last clause assumes `𝒲` permutation-invariant, the setting in which Lemma 9.1 defines "symmetric": it is what lets a
list of types determine `𝒲`. -/
theorem lemma_9_3 (q : ℕ) [NeZero q] (hq : q.Prime) :
    ∃ (P : Program) (b C e : ℕ), NoProbe P ∧ NoCoin P ∧
      ∀ (d : ℕ) (_ : 1 ≤ d) (𝒲 : Finset (Fin d → ZMod q)) (𝒜 : Finset (ZMod q))
        (ζ : CyclotomicField q ℚ) (_ : IsPrimitiveRoot ζ q)
        (c : (Fin d → ZMod q) → ZMod q → CyclotomicField q ℚ) (_ : IsDeltaExpansion ζ c)
        (_ : IsSymmetric c) (_ : HasSupport c (𝒲 : Set (Fin d → ZMod q)) (𝒜 : Set (ZMod q))),
        ∃ M : ℕ, 0 < M ∧ M ≤ bigM q d ∧
          ∀ (p : ℕ) [Fact p.Prime], p ≡ 1 [MOD q] → M < p → ∀ γ : ZMod p, IsPrimitiveRoot γ q →
            (∃ c' : (Fin d → ZMod q) → ZMod q → ZMod p, IsDeltaExpansion γ c' ∧ IsSymmetric c' ∧
              HasSupport c' (𝒲 : Set (Fin d → ZMod q)) (𝒜 : Set (ZMod q))) ∧
            (IsPermInvariant (𝒲 : Set (Fin d → ZMod q)) →
              ∀ tys : List (ZMod q → ℕ), (∀ τ, τ ∈ tys ↔ ∃ w ∈ 𝒲, typeOf w = τ) →
              ∀ W ≥ b * (Nat.log2 (d + 1) + Nat.log2 (Nat.log2 p + 1) + 1),
              ∃ (t : ℕ) (st : State W), t ≤ C * (d + Nat.log2 p + 1) ^ e ∧
                Accepts P [] zeroTape (coeffInput q d p γ.val tys 𝒜) t st ∧
                IsDeltaExpansion γ (decodedCoeff p st tys 𝒲 𝒜) ∧
                IsSymmetric (decodedCoeff p st tys 𝒲 𝒜) ∧
                HasSupport (decodedCoeff p st tys 𝒲 𝒜)
                  (𝒲 : Set (Fin d → ZMod q)) (𝒜 : Set (ZMod q))) := by sorry

end ModFormPIR
