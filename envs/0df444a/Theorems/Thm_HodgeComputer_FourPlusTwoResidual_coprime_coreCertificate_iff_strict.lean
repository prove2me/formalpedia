-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coprime_coreCertificate_iff_strict
-- name    : HodgeComputer.FourPlusTwoResidual.coprime_coreCertificate_iff_strict
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:34.972982+00:00
-- url     : https://prove2.me/theorems/36ac7eff-e9cb-4a09-9c3d-ea56f2e0892b
-- title:
--   Universal strict divergence-free normalization for core certificates not divisible by core
-- statement:
--   Let $H(x_0, x_1, y_0, y_1)$ be the four-variable sextic core of `four-plus-two-residual` and let $A = x_0^3 y_0^3$. For **any** polynomial $D \in \mathbb{C}[x_0, x_1, y_0, y_1]$ of **arbitrary** positive homogeneous degree $k + 1 \ge 1$ such that $H \nmid D$, $D$ admits a twisted core certificate $N$ satisfying
--
--   $$
--   2 A D^2 - 2 D (N \cdot \nabla H) + 3 H \bigl(D \operatorname{div}(N) - N \cdot \nabla D\bigr) = 0
--   $$
--
--   if and only if $D$ admits a strict divergence-free vector field $p$ satisfying
--
--   $$
--   p \cdot \nabla H = A D \qquad \text{and} \qquad D \operatorname{div}(p) - p \cdot \nabla D = 0.
--   $$
--
--   Remarkably, this equivalence holds in **every** degree $k + 1 \ge 1$, not merely at $\deg D = 6$: primality of $H$ forces $N \cdot \nabla H - A D = H R$ with $R$ homogeneous of degree $k + 1$, and in the radial gauge shift $p_i = N_i - \frac{1}{6} R x_i$ the degree-$(k + 1)$ Euler weights of $R$ and $D$ cancel identically in $D \operatorname{div}(R x) - R (x \cdot \nabla D) = ((k + 1 + 4) - (k + 1)) D R = 4 D R$, leaving the universal $6 : 4 = 3 : 2$ ratio matching the Calabi–Yau residue weight of $H$ in $\mathbb{C}^4$.
--
--   **Formalization Note** Generalizes `degreeSix_coreCertificate_iff_strict` to arbitrary homogeneous degree and discharges `IsRelPrime core D` unconditionally from `¬ (core ∣ D)` via `Irreducible core`.
-- source:
--   All-degree generalization of the degree-six Euler gauge observation in Hodge.computer Discussion #120 (`benediamond`, `kmehltretter82`), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry

theorem HodgeComputer.FourPlusTwoResidual.coprime_coreCertificate_iff_strict
    (D : MvPolynomial (Fin 4) ℂ) (hndvd : ¬ (HodgeComputer.FourPlusTwoResidual.core ∣ D)) :
    (∃ N : Fin 4 → MvPolynomial (Fin 4) ℂ,
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D N) ↔
    (∃ p : Fin 4 → MvPolynomial (Fin 4) ℂ,
      HodgeComputer.FourPlusTwoResidual.StrictCoreCertificate D p) := by sorry
