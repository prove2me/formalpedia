-- Prove2me | Theorems.Thm_MasulloGRH_dynin_mityagin
-- name    : MasulloGRH.dynin_mityagin
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T04:40:13.416777+00:00
-- url     : https://prove2.me/theorems/42e36e24-3944-4259-bb89-5a117ca54295
-- title:
--   Theorem 4.1.2.6 — Dynin–Mityagin: Schauder bases of nuclear spaces are absolute
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$. A sequence $(x_m)_{m\ge0}$ in $E$ with continuous linear functionals $(f_m)_{m\ge0}$ is a **Schauder basis** if $f_m(x_n)=\delta_{m,n}$ and $u=\sum_{m\ge0}f_m(u)x_m$ in $E$ for every $u\in E$. It is **equicontinuous** if the projections $P_k=\sum_{m\le k}f_m\cdot x_m$ form an equicontinuous sequence, and **absolute** if for every continuous seminorm $q$ there is a continuous seminorm $q'$ with $\sum_{m\ge0}q(f_m(u)x_m)\le q'(u)$ for all $u$.
--
--   Let $(x_m)$ be a Schauder basis of $E$ with coefficient functionals $(f_m)$.
--
--   1. If $E$ is nuclear and the basis is equicontinuous, then the basis is absolute.
--   2. If $E$ is a nuclear Fréchet space, then the basis is absolute.
--   3. If $E$ is a strict inductive limit of a sequence of nuclear Fréchet spaces, then the basis is absolute.
--
--   In nuclear spaces every basis expansion therefore converges absolutely with respect to every continuous seminorm. The draft applies item 3 to its spaces of $\theta$-functions.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 4, §4.1.2, Theorem 4.1.2.6 (Dynin-Mityagin), p. 161

import Definitions.Def_MasulloGRH_SchauderBases

set_option autoImplicit false

namespace MasulloGRH

theorem dynin_mityagin (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) :
    (IsNuclear E → IsEquicontinuousBasis x f → IsAbsoluteBasis x f) ∧
    (IsNuclear E → IsFrechet E → IsAbsoluteBasis x f) ∧
    (IsStrictLFOfNuclearFrechet E → IsAbsoluteBasis x f) := by sorry

end MasulloGRH
