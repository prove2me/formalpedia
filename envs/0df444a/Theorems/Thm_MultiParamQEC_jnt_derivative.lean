-- Prove2me | Theorems.Thm_MultiParamQEC_jnt_derivative
-- name    : MultiParamQEC.jnt_derivative
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:49.436026+00:00
-- url     : https://prove2.me/theorems/be807a5d-41a7-42fb-9a5d-5575eaf1bec6
-- title:
--   p.8 — derivative of the JNT-QEC state: $2\mathrm{Re}\langle c|\partial_j\psi_{\omega=0}\rangle=2T\,\mathrm{Im}\langle c|(G_j\otimes\mathbb 1)|c_0\rangle$
-- statement:
--   Let $\Pi_C$ be the orthogonal projection onto a code space $\mathcal H_C\subseteq\mathcal H_S\otimes\mathcal H_A$, $|\psi_{\rm in}\rangle\in\mathcal H_C$, $T\in\mathbb R$, and let $|\psi_{\boldsymbol\omega}\rangle$ be the JNT-QEC evolution (20). Write $|c_0\rangle=|\psi_{\boldsymbol\omega=0}\rangle$. Then for every $|c\rangle\in\mathcal H_C$ and every $j$,
--   $$2\,\mathrm{Re}\,\langle c|\partial_j\psi_{\boldsymbol\omega=0}\rangle=2T\,\mathrm{Im}\,\langle c|(G_j\otimes\mathbb 1_{\dim\mathcal H_A})|c_0\rangle .$$
--
--   This identity converts the frame form (19) of the Matsumoto bound into the fixed-code program (21).
--
--   Differences from the source:
--   - encoding: H_S ⊗ H_A with dim H_S = d, H_A an ancilla of any finite dimension → index type Fin d × Fin a (probe first), operators X ⊗ 1 as X ⊗ₖ 1_a, code space given by its orthogonal projection PiC; reason: Lean convention; same instances
--   - generalization: H_C a code space satisfying the QEC condition (6), Hermitian generators G_j, total time T > 0 → any orthogonal projection PiC, any matrices G_j, any real T; reason: the identity is a computation of the derivative of (20) that uses only Π_C c = c and Π_C ψ_in = ψ_in; every instance of the source satisfies the Lean hypotheses
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.2, p.8, first line

import Mathlib
import Definitions.Def_MultiParamQEC_JNTQEC

open scoped ComplexOrder Matrix Kronecker

namespace MultiParamQEC

/-- **Derivative of the JNT-QEC state at `ω = 0`** (Górecki–Zhou–Jiang–Demkowicz-Dobrzański,
arXiv:1901.00896v4, p.8, first line: "for any `|c_i⟩ ∈ H_C` we have
`2Re⟨c_i|∂_j|ψ_{ω=0}⟩ = 2T Im⟨c_i|(G_j ⊗ 1_{dim(H_A)})|c_0⟩`").

For the effective evolution (20) `|ψ_ω⟩ = exp(−iT Σ_j ω_j Π_C (G_j ⊗ 1) Π_C)|ψ_in⟩` with
`|ψ_in⟩ ∈ H_C`, and `|c_0⟩ = |ψ_{ω=0}⟩`, every `|c⟩ ∈ H_C` satisfies
`2Re⟨c|∂_jψ_{ω=0}⟩ = 2T Im⟨c|(G_j ⊗ 1)|c_0⟩`. The derivative is the genuine derivative of the
family at `ω = 0`. -/
theorem jnt_derivative {d a P : ℕ} (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (PiC : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ) (hPi : IsCodeProjection PiC)
    (ψin : Fin d × Fin a → ℂ) (hin : PiC *ᵥ ψin = ψin) (T : ℝ) (j : Fin P)
    (c : Fin d × Fin a → ℂ) (hc : PiC *ᵥ c = c) :
    2 * (star c ⬝ᵥ partialDeriv (jntState G PiC ψin T) 0 j).re =
      2 * T * (star c ⬝ᵥ ((G j ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)) *ᵥ
        jntState G PiC ψin T 0)).im := by sorry

end MultiParamQEC
