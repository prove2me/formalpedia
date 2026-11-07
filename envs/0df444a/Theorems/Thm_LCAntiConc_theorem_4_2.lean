-- Prove2me | Theorems.Thm_LCAntiConc_theorem_4_2
-- name    : LCAntiConc.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:00.477674+00:00
-- url     : https://prove2.me/theorems/cb656f24-a0f4-419e-a725-d3b672d0827c
-- title:
--   Theorem 4.2 — certificates from bounded Stein kernels at degree $O(m+\delta^{-30})$
-- statement:
--   Let $A_1,A_2,A_3>0$. There are $\delta_0>0$ and $C>0$ such that for every $0<\delta<\delta_0$ the following holds. Let $X\in\mathbb R^d$ be a random vector such that
--
--   1. $X$ has a $(T,\delta^4)$-bounded approximate Stein kernel in the sense of Definition B.1 (constant $A_2$ in (B.3)) with $T\le A_1\log(1/\delta)$, and
--   2. $X$ is $\delta$-strengthened anti-concentrated at degree $m$ in the sense of Definition 4.1 (constant $A_3$), with polynomial $q$.
--
--   Then for some $D\le C(m+\delta^{-30})$,
--
--   $$\{\|v\|_2^2=1\}\vdash_D\ \mathop{\mathbb E}_X q(\langle X,v\rangle)\le C\,\delta.\tag{4.1}$$
--
--   This is the general form of the main theorem: any distribution with a bounded approximate Stein kernel and a strengthened anti-concentration witness has a dimension-independent certificate.
--
--   Differences from the source:
--   - reading: O(·) inside the hypotheses ((O(log 1/δ), δ⁴)-kernel, the O(δ) and O(δ^{-2r}) of Definition 4.1, the O(·) of (B.3)) → universally quantified parameters A₁, A₂, A₃ > 0; the conclusion's constants depend only on them; reason: an O(·) in a hypothesis fixes a class with some constant; the conclusion must hold for each such class
--   - reading: "δ smaller than a small enough absolute constant" → ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀); reason: the usual meaning of the phrase
--   - reading: "for D = O(m + δ⁻³⁰)" and "⩽ O(δ)" → ∃ D ≤ C(m + δ⁻³⁰) with the bound C δ, one constant C; reason: sum-of-squares proofs are monotone in the degree; one constant for several O's is equivalent
--   - reading: "degree-m polynomial" in Definition 4.1 → deg q ≤ m; reason: Lemmas 4.12–4.13 say "for some m ≤ …" and Theorem 4.2 uses m only through D = O(m + δ^{-30}); ≤ is the reading under which the chain fits
--   - encoding: random vector X ∈ ℝ^d → its law μ, a probability measure on EuclideanSpace ℝ (Fin d); reason: Euclidean norm and inner product; same instances
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Theorem 4.2, (4.1), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_LCAntiConc_IsStrengthenedAC
import Definitions.Def_LCAntiConc_IsStein
import Definitions.Def_LCAntiConc_SphereSoSLe
import Definitions.Def_LCAntiConc_expectQ

namespace LCAntiConc

open MeasureTheory

/-- **Theorem 4.2** (Certificates from bounded Stein kernels). Let `0 < δ` be smaller than a small
enough absolute constant and let `X ∈ ℝ^d` be a random vector such that (1) `X` has an
`(O(log 1/δ), δ⁴)`-bounded approximate Stein kernel (Definition B.1), and (2) `X` is
`δ`-strengthened anti-concentrated at degree `m` (Definition 4.1), with polynomial `q`. Then, for
`D = O(m + δ⁻³⁰)`, `{‖v‖₂² = 1} ⊢_D 𝔼_X q(⟨X, v⟩) ≤ O(δ)` (4.1).

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Theorem 4.2, p.17 (PDF p.19).

**Formalization Note** The constants inside the hypotheses are parameters (`A₁` in
`T ≤ A₁ log(1/δ)`, `A₂` in (B.3), `A₃` in Definition 4.1); `δ₀` and `C` depend only on them
and come before `δ`, `d`, the law, `m`, `q` and the kernel. "For `D = O(m + δ⁻³⁰)`" is
`∃ D ≤ C(m + δ⁻³⁰)`; sum-of-squares proofs are monotone in the degree. -/
theorem theorem_4_2 (A₁ A₂ A₃ : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hA₃ : 0 < A₃) :
    ∃ δ₀ > 0, ∃ C > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (m : ℕ)
        (q : Polynomial ℝ) (T : ℝ) (H : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
        (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      T ≤ A₁ * Real.log (1 / δ) → IsStein μ T (δ ^ 4) A₂ H r → IsStrengthenedAC μ δ m A₃ q →
      ∃ D : ℕ, (D : ℝ) ≤ C * (m + δ ^ (-30 : ℤ)) ∧ SphereSoSLe D (expectQ μ q) (C * δ) := by sorry

end LCAntiConc
