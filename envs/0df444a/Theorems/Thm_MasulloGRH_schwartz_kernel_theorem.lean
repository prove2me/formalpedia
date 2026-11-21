-- Prove2me | Theorems.Thm_MasulloGRH_schwartz_kernel_theorem
-- name    : MasulloGRH.schwartz_kernel_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T22:43:04.474171+00:00
-- url     : https://prove2.me/theorems/38071772-3fca-4ef7-80a0-a0db6097b218
-- title:
--   Theorem C.2.4.18 — Schwartz Kernel Theorem for continuous bilinear forms on a nuclear space
-- statement:
--   Let $E$ and $F$ be Hausdorff locally convex spaces over $\mathbb C$ with $E$ nuclear, and let $B\colon E\times F\to\mathbb C$ be a continuous bilinear form. Then there are an equicontinuous sequence $(\varphi_m)_{m\ge0}$ of continuous linear functionals on $E$, an equicontinuous sequence $(\psi_m)_{m\ge0}$ of continuous linear functionals on $F$, and an absolutely summable sequence of complex numbers $(\lambda_m)_{m\ge0}$ such that
--
--   $$B(x,y)=\sum_{m\ge0}\lambda_m\,\varphi_m(x)\,\psi_m(y),$$
--
--   the series converging uniformly for $(x,y)$ in $S\times T$, for all bounded subsets $S\subset E$ and $T\subset F$.
--
--   This is the abstract kernel theorem: on a nuclear space every continuous bilinear form is nuclear. The draft uses it to represent operators on spaces of $\theta$-functions by kernels and to define their traces.
--
--   **Formalization Note** The convergence of the series is convergence of the partial sums over $m<k$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4, Theorem C.2.4.18 (Schwartz Kernel Theorem), eq. (C.2.4.8), pp. 690–691

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem schwartz_kernel_theorem (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsNuclear E) (hF : IsHLCS F)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hB : Continuous (fun p : E × F => B p.1 p.2)) :
    ∃ (φ : ℕ → StrongDual ℂ E) (ψ : ℕ → StrongDual ℂ F) (c : ℕ → ℂ),
      Equicontinuous (fun m => (φ m : E → ℂ)) ∧ Equicontinuous (fun m => (ψ m : F → ℂ)) ∧
      Summable (fun m => ‖c m‖) ∧
      ∀ (S : Set E) (T : Set F), Bornology.IsVonNBounded ℂ S → Bornology.IsVonNBounded ℂ T →
        TendstoUniformlyOn
          (fun (k : ℕ) (p : E × F) => ∑ m ∈ Finset.range k, c m * φ m p.1 * ψ m p.2)
          (fun p : E × F => B p.1 p.2) Filter.atTop (S ×ˢ T) := by sorry

end MasulloGRH
