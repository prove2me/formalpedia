-- Prove2me | Theorems.Thm_KnownFidelity_Rank_eq_16
-- name    : KnownFidelity.Rank.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:22.765463+00:00
-- url     : https://prove2.me/theorems/45453ac5-11db-43e3-b377-2e8c34cf1bf7
-- title:
--   §3.2, Eq. (16) — random-purification channel: $\mathcal P_{n,d,s}(\rho^{\otimes n})=\mathbb E_W(|\psi_{\rho,W}\rangle\langle\psi_{\rho,W}|)^{\otimes n}$
-- statement:
--   For all $n,d,s\in\mathbb N$ there is a quantum channel $\mathcal P_{n,d,s}$ from $(\mathbb C^d)^{\otimes n}$ to $(\mathbb C^d\otimes\mathbb C^s)^{\otimes n}$, depending only on $n,d,s$, such that for every state $\rho$ on $\mathbb C^d$ of rank at most $s$
--
--   $$\mathcal P_{n,d,s}(\rho^{\otimes n})=\mathbb E_W\big(|\psi_{\rho,W}\rangle\langle\psi_{\rho,W}|\big)^{\otimes n},$$
--
--   where each $|\psi_{\rho,W}\rangle\in\mathbb C^d\otimes\mathbb C^s$ is a purification of $\rho$ ($\mathrm{tr}_2|\psi_{\rho,W}\rangle\langle\psi_{\rho,W}|=\rho$), and one common random purification appears in all $n$ factors.
--
--   This is the random-purification channel of Tang–Wright–Zhandry in the rank-dependent form of Lowe–Tan [9, Theorem 2.5], which the paper imports. It turns $n$ copies of a mixed state into $n$ copies of a random purification, to which Lemma 3.1 applies.
--
--   **Formalization Note** $\mathbb E_W$ is an integral against a probability measure $\mu$ on vectors $\psi\in\mathbb C^d\otimes\mathbb C^s$ that is almost surely a purification of $\rho$; the channel is a finite Kraus family, chosen before $\rho$.
--
--   Differences from the source:
--   - encoding: E_W over the randomness W of [9, Theorem 2.5] → ∃ probability measure μ on ℂ^d ⊗ ℂ^s (the law of ψ_{ρ,W}), μ-a.s. a purification of ρ, with P(ρ^{⊗n}) = ∫ (ψψ*)^{⊗n} dμ (entrywise); reason: the statement and its use depend only on the law of the random purification
--   - encoding: a channel → QAlgorithms.IsChannel (finite normalized Kraus family); reason: in finite dimension these are exactly the completely positive trace-preserving maps
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §3.2, Eq. (16) (unnumbered statement, cited from Lowe–Tan [9, Theorem 2.5]), p. 7 (PDF p. 9)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_GradientMethods

open MeasureTheory
open scoped Matrix ComplexOrder

namespace KnownFidelity.Rank

/-- **§3.2, Eq. (16): the random-purification channel.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §3.2, Eq. (16) (unnumbered statement), printed p. 7 (PDF p. 9): "The
random-purification channel of Tang–Wright–Zhandry [13], in the form of Lowe–Tan [9,
Theorem 2.5], gives a channel P_{n,d,s} such that P_{n,d,s}(ρ^{⊗n}) = E_W (|ψ_{ρ,W}⟩⟨ψ_{ρ,W}|)^{⊗n}
(16) for every state of rank at most s. Each |ψ_{ρ,W}⟩ ∈ C^d ⊗ C^s purifies ρ, and one common
random purification appears in all n factors. The channel depends only on n, d, s."

For all `n, d, s` there is a quantum channel `P` from `(ℂ^d)^{⊗n}` to `(ℂ^d ⊗ ℂ^s)^{⊗n}` such
that for every state `ρ` on `ℂ^d` of rank at most `s` there is a probability measure `μ` on
vectors `ψ ∈ ℂ^d ⊗ ℂ^s`, almost surely a purification of `ρ` (`tr₂ |ψ⟩⟨ψ| = ρ`), with
`P(ρ^{⊗n}) = ∫ (|ψ⟩⟨ψ|)^{⊗n} dμ(ψ)`.

**Formalization Note.** The paper imports this from [9, Theorem 2.5]; it is stated here so that
the mission's goal does not rest on an unproved hypothesis. The channel is chosen before `ρ`;
`E_W` is an expectation over the law `μ` of the random purification `ψ_{ρ,W}`. A channel is the
platform's `QAlgorithms.IsChannel` (finite normalized Kraus family, i.e. CPTP in finite
dimension), the partial trace over the purifying register is `QAlgorithms.traceRight`, and the
average is taken entrywise (each entry is bounded by `1` almost surely, so the integrals are
genuine). -/
theorem eq_16 (n d s : ℕ) :
    ∃ P : QAlgorithms.Superop (Fin n → Fin d) (Fin n → Fin d × Fin s),
      QAlgorithms.IsChannel P ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix ρ → ρ.rank ≤ s →
        ∃ μ : Measure (Fin d × Fin s → ℂ), IsProbabilityMeasure μ ∧
          (∀ᵐ ψ ∂μ, QAlgorithms.traceRight (Matrix.vecMulVec ψ (star ψ)) = ρ) ∧
          P (QAlgorithms.piKron n ρ) =
            Matrix.of fun x y => ∫ ψ, QAlgorithms.piKron n (Matrix.vecMulVec ψ (star ψ)) x y ∂μ := by sorry

end KnownFidelity.Rank
