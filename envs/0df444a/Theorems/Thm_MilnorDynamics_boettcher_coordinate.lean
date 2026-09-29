-- Prove2me | Theorems.Thm_MilnorDynamics_boettcher_coordinate
-- name    : MilnorDynamics.boettcher_coordinate
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T11:07:52.157704+00:00
-- url     : https://prove2.me/theorems/ab6bcecc-f444-45ae-a563-90c8972969ba
-- title:
--   Theorem 9.1 (Böttcher) — a superattracting germ is conjugate to $w\mapsto w^n$
-- statement:
--   **Böttcher's theorem.** Let $f$ be holomorphic near $0$ with a superattracting fixed point of local degree $n\ge2$:
--   $$
--   f(z)=a_nz^n+a_{n+1}z^{n+1}+\cdots,\qquad a_n\neq0 .
--   $$
--   Then there is a local holomorphic change of coordinate $w=\phi(z)$ with $\phi(0)=0$ which conjugates $f$ to the $n$-th power map throughout some neighbourhood of zero:
--   $$
--   \phi(f(z))=\phi(z)^n .
--   $$
--   Furthermore $\phi$ is unique up to multiplication by an $(n-1)$-st root of unity.
--
--   Applied at $\infty$ to a polynomial of degree $d\ge2$ (local degree $n=d$), this is the starting point of polynomial dynamics: the Böttcher coordinate near $\infty$ yields Green's function, equipotentials and external rays.
--
--   **Formalization Note** "$f(z)=a_nz^n+\cdots$ with $a_n\neq0$'' is encoded as $f(z)=z^n g(z)$ on a disk $\{|z|<r\}$ with $g$ holomorphic there and $g(0)\neq0$. "Local change of coordinate'' is encoded as holomorphic and injective on an open set $W$ containing $U\cup f(U)$ for a neighbourhood $U$ of $0$; uniqueness is for germs at $0$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §9, p. 90, Theorem 9.1 (Böttcher [1904]), with f as in (9:1); stated in a local coordinate with the fixed point at 0

import Mathlib
import Definitions.Def_MilnorDynamics_Polynomials

open scoped OnePoint Topology Polynomial
open Filter Set

namespace MilnorDynamics

theorem boettcher_coordinate (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r)) (n : ℕ) (hn : 2 ≤ n)
    (hlocal : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 r) ∧ g 0 ≠ 0 ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r, f z = z ^ n * g z) :
    ∃ φ : ℂ → ℂ, (∃ U W : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧ U ⊆ Metric.ball 0 r ∧ IsOpen W ∧
        U ∪ f '' U ⊆ W ∧ DifferentiableOn ℂ φ W ∧ InjOn φ W ∧ φ 0 = 0 ∧
        ∀ z ∈ U, φ (f z) = φ z ^ n) ∧
      ∀ ψ : ℂ → ℂ, (∃ U W : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧ U ⊆ Metric.ball 0 r ∧ IsOpen W ∧
          U ∪ f '' U ⊆ W ∧ DifferentiableOn ℂ ψ W ∧ InjOn ψ W ∧ ψ 0 = 0 ∧
          ∀ z ∈ U, ψ (f z) = ψ z ^ n) →
        ∃ ω : ℂ, ω ^ (n - 1) = 1 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ψ z = ω * φ z := by sorry

end MilnorDynamics
