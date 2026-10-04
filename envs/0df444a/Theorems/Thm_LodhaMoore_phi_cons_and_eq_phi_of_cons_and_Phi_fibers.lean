-- Prove2me | Theorems.Thm_LodhaMoore_phi_cons_and_eq_phi_of_cons_and_Phi_fibers
-- name    : LodhaMoore.phi_cons_and_eq_phi_of_cons_and_Phi_fibers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T21:04:01.289989+00:00
-- url     : https://prove2.me/theorems/cc65dd74-89e1-441d-a977-285f27e27ef4
-- title:
--   §2 — φ is the unique solution of its defining equations, and Φ is one-to-one off the eventually constant sequences, where it is two-to-one
-- statement:
--   For every infinite binary sequence $\xi$: $\phi(0\xi) = 1/(1 + 1/\phi(\xi))$ and $\phi(1\xi) = 1 + \phi(\xi)$ in $[0, \infty]$, and every function $\psi$ from infinite binary sequences to $[0, \infty]$ satisfying these two equations equals $\phi$. If $\xi$ is not eventually constant, it is the only sequence with its value of $\Phi$. If $\xi$ is eventually constant, exactly two sequences have its value of $\Phi$. For every finite $s$, $\Phi(s0\bar1) = \Phi(s1\bar0)$, and $\Phi(\bar0) = \Phi(\bar1) = \infty$.
--
--   **Formalization Note.** The paper glosses "eventually constant" as "(i.e. $r_k = \infty$ for some $k$)"; $r_k$ is not defined anywhere in the paper, so "eventually constant" (`EventuallyConst`) is formalized directly.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 3, §2

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem phi_cons_and_eq_phi_of_cons_and_Phi_fibers :
    (∀ ξ, phi (Stream'.cons false ξ) = (1 + (phi ξ)⁻¹)⁻¹) ∧ (∀ ξ, phi (Stream'.cons true ξ) = 1 + phi ξ) ∧
    (∀ ψ : Stream' Bool → ENNReal, (∀ ξ, ψ (Stream'.cons false ξ) = (1 + (ψ ξ)⁻¹)⁻¹) →
      (∀ ξ, ψ (Stream'.cons true ξ) = 1 + ψ ξ) → ψ = phi) ∧
    (∀ ξ, ¬ EventuallyConst ξ → ∀ η, Phi η = Phi ξ → η = ξ) ∧
    (∀ ξ, EventuallyConst ξ → {η | Phi η = Phi ξ}.ncard = 2) ∧
    (∀ s : Seq, Phi (s ++ₛ Stream'.cons false (Stream'.const true)) =
      Phi (s ++ₛ Stream'.cons true (Stream'.const false))) ∧
    Phi (Stream'.const false) = OnePoint.infty ∧ Phi (Stream'.const true) = OnePoint.infty := by
  sorry

end LodhaMoore
