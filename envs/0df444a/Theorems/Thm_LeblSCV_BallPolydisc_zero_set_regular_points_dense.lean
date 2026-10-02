-- Prove2me | Theorems.Thm_LeblSCV_BallPolydisc_zero_set_regular_points_dense
-- name    : LeblSCV.BallPolydisc.zero_set_regular_points_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:24:36.874414+00:00
-- url     : https://prove2.me/theorems/b6a1386d-de77-4570-b3b2-3802d68d00c6
-- title:
--   Theorem 1.6.2 — the zero set of a holomorphic function is a graph on an open dense subset
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain, $f \in \mathcal{O}(U)$ not identically zero, and $N = f^{-1}(0) \subset U$. Then there is a subset $N_{\mathrm{reg}} \subset N$, open and dense in $N$ for the subspace topology, such that at each $p \in N_{\mathrm{reg}}$, after possibly reordering the variables, $N$ can be written in some neighbourhood of $p$ as a graph
--   $$z_n = g(z_1, \dots, z_{n-1})$$
--   for a holomorphic function $g$.
--
--   Points where the zero set is such a graph are its regular points; the theorem says the zero set of a holomorphic function is a complex hypersurface at most of its points, and in particular is large when $n \ge 2$.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; $N$ is `U ∩ f ⁻¹' {0}`. "Open in $N$" is `Nreg = O ∩ N` for an open `O`; "dense in $N$" is `N ⊆ closure Nreg`. "After reordering, $z_n = g(z_1, \dots, z_{n-1})$" is encoded by choosing the solved-for variable `j : Fin n`: the remaining coordinates are indexed by the subtype `{i // i ≠ j}`, and there are an open neighbourhood $W$ of $p$, an open set $W'$ of the remaining coordinates containing the projection of $W$, and $g$ holomorphic on $W'$ such that, for $z \in W$, $z \in N \iff z_j = g\big((z_i)_{i \ne j}\big)$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 42, Theorem 1.6.2

import Mathlib

namespace LeblSCV.BallPolydisc

/-- Theorem 1.6.2 (Lebl, p. 42). Let `U ⊆ ℂⁿ` be a domain, `f` holomorphic on `U` and not
identically zero, `N = f⁻¹(0) ⊆ U`. There is a subset `N_reg ⊆ N`, open and dense in `N`
(subspace topology), such that at each `p ∈ N_reg`, for some variable `z_j` (the reordering),
`N` is locally near `p` the graph `z_j = g(z_i : i ≠ j)` of a holomorphic function `g`. -/
theorem zero_set_regular_points_dense {n : ℕ} (U : Set (Fin n → ℂ))
    (hUo : IsOpen U) (hUc : IsConnected U)
    (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f U) (hf0 : ∃ z ∈ U, f z ≠ 0) :
    ∃ Nreg : Set (Fin n → ℂ), Nreg ⊆ U ∩ f ⁻¹' {0} ∧
      (∃ O : Set (Fin n → ℂ), IsOpen O ∧ Nreg = O ∩ (U ∩ f ⁻¹' {0})) ∧
      U ∩ f ⁻¹' {0} ⊆ closure Nreg ∧
      ∀ p ∈ Nreg, ∃ j : Fin n, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧
        ∃ W' : Set ({i : Fin n // i ≠ j} → ℂ), IsOpen W' ∧
          ∃ g : ({i : Fin n // i ≠ j} → ℂ) → ℂ, DifferentiableOn ℂ g W' ∧
            ∀ z ∈ W, (fun i : {i : Fin n // i ≠ j} => z i.1) ∈ W' ∧
              (z ∈ U ∩ f ⁻¹' {0} ↔ z j = g (fun i : {i : Fin n // i ≠ j} => z i.1)) := by sorry

end LeblSCV.BallPolydisc
