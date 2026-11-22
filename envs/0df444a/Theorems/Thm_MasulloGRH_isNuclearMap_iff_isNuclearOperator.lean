-- Prove2me | Theorems.Thm_MasulloGRH_isNuclearMap_iff_isNuclearOperator
-- name    : MasulloGRH.isNuclearMap_iff_isNuclearOperator
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:56.311431+00:00
-- url     : https://prove2.me/theorems/015605e8-29bb-4c9d-a4b9-21738fae0e2b
-- title:
--   On a Hilbert space, Grothendieck-nuclear endomorphisms are the nuclear (trace-class) operators, and the nuclear trace is $\sum_\phi\langle T\phi,\phi\rangle$
-- statement:
--   **Nuclear endomorphisms of a Hilbert space: the locally convex and the Hilbert space notions agree, and so do the traces.**
--
--   Let $H$ be a complex Hilbert space and $T$ a bounded operator on $H$.
--
--   - $T$ is a **nuclear map** in the sense of locally convex spaces (Grothendieck) if $T=\sum_n\lambda_n\langle\cdot,\varphi_n\rangle y_n$ with $\sum_n|\lambda_n|<\infty$, $(\varphi_n)$ an equicontinuous sequence in $H'$ and $(y_n)$ contained in a Banach disc of $H$ (a *nuclear representation* of $T$).
--   - $T$ is a **nuclear (trace-class) operator** in the Hilbert space sense used on the platform if there are sequences $(x_m)$, $(y_m)$ in $H$ with $\sum_m\|x_m\|\,\|y_m\|<\infty$ and $Tu=\sum_m\langle u,x_m\rangle y_m$ for all $u\in H$; its **trace** is $\operatorname{Trace}(T)=\sum_{\phi\in\Sigma}\langle T\phi,\phi\rangle_H$ for an orthonormal basis $\Sigma$ of $H$.
--
--   Then:
--
--   1. $T$ is a nuclear map if and only if $T$ is a nuclear operator in the Hilbert space sense.
--   2. For every nuclear representation $T=\sum_m\lambda_m\langle\cdot,\varphi_m\rangle y_m$ the series $\sum_m\lambda_m\varphi_m(y_m)$ converges absolutely and
--   $$\sum_m\lambda_m\,\langle y_m,\varphi_m\rangle_{H,H'}=\operatorname{Trace}(T)=\sum_{\phi\in\Sigma}\langle T\phi,\phi\rangle_H ,$$
--   i.e. the nuclear trace of (C.3.2.2) is the trace of Definition C.3.4.2.
--
--   The paper states this as: nuclear endomorphisms of a Hilbert space are exactly the trace-class operators, a familiar example of the general theory of §C.3.1–C.3.2. The statement lets one transfer results between the locally convex theory (ideal property, trace through a factorization) and the Hilbert space theory (trace norm, orthonormal bases).
--
--   **Formalization Note.** `IsNuclearMap` and `IsNuclearRepr` are from `Def_MasulloGRH_NuclearMap`; `IsNuclearOperator` and `operatorTrace` are from `Def_MasulloGRH_HilbertNuclear` (the trace is the sum over one fixed orthonormal basis, which for nuclear operators does not depend on the basis by the platform theorem `MasulloGRH.nuclear_trace_hasSum_hilbertBasis`). Part 2 is stated for every nuclear representation, so no separate nuclear-trace function is needed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 697, §C.3.4 (opening paragraph), with (C.3.2.2) (p. 694) and Definition C.3.4.2(1); classical reference: C. S. Kubrusly, Trace-Class and Nuclear Operators, Concrete Operators 9 (2022), pp. 53-69, Thm. 6.1

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear
import Definitions.Def_MasulloGRH_NuclearMap

open Filter Topology
set_option autoImplicit false

namespace MasulloGRH

theorem isNuclearMap_iff_isNuclearOperator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    (IsNuclearMap T ↔ IsNuclearOperator T) ∧
      ∀ (c : ℕ → ℂ) (φ : ℕ → StrongDual ℂ H) (y : ℕ → H), IsNuclearRepr T c φ y →
        Summable (fun m => ‖c m * φ m (y m)‖) ∧
        HasSum (fun m => c m * φ m (y m)) (operatorTrace T) := by sorry

end MasulloGRH
