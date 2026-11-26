-- Prove2me | Theorems.Thm_LefebvreVariations_fiducial_d3
-- name    : LefebvreVariations.fiducial_d3
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:12:51.467899+00:00
-- url     : https://prove2.me/theorems/1dfa31aa-8f26-46d0-bd30-1096a57ce984
-- title:
--   Lefebvre's variations, No. 12 — on a theme by Zauner: a Weyl–Heisenberg SIC fiducial in dimension 3
-- statement:
--   This is Zauner's conjecture in dimension $3$, with an explicit fiducial vector.
--
--   Let $\omega=e^{2\pi i/3}$ and, for $a,b\in\mathbb Z/3\mathbb Z$, let $D_{a,b}$ act on $\psi:\mathbb Z/3\mathbb Z\to\mathbb C$ by $(D_{a,b}\psi)(x)=\omega^{bx}\psi(x+a)$, the Weyl–Heisenberg displacements. The unit vector
--
--   $$
--   \psi=\tfrac1{\sqrt2}\,(0,\;1,\;-1)
--   $$
--
--   is a Weyl–Heisenberg fiducial: for every $(a,b)\neq(0,0)$,
--
--   $$
--   \big|\langle\psi,\,D_{a,b}\psi\rangle\big|^2=\frac1{d+1}=\frac14 .
--   $$
--
--   Equivalently, the nine vectors $D_{a,b}\psi$ form a symmetric informationally complete POVM (SIC-POVM) in $\mathbb C^3$. Zauner's conjecture asserts that such a fiducial exists in every dimension $d$; the cases $d=1,2$ are already on the platform, and this settles $d=3$ in the same formulation.
--
--   **Formalization Note** The statement has exactly the form of `WeylHeisenbergSIC.fiducial_exists` at $d=3$: the displacement phase is `ZMod.stdAddChar (b*x)`, and the right-hand side is written $((3:\mathbb N)+1)^{-1}$.
--
--   **Why this is a variation.** This varies Zauner's conjecture on SIC-POVMs, which asserts that a Weyl–Heisenberg fiducial vector exists in every dimension $d$. It is the first non-trivial size, $d=3$, where the vector $(0,1,-1)/\sqrt2$ has squared overlap $1/(d+1)=1/4$ with all eight nonidentity displacements. It is one of the finite cases that the general conjecture must contain and that guides the search for a uniform construction.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   G. Zauner, Quantendesigns – Grundzüge einer nichtkommutativen Designtheorie, PhD thesis, University of Vienna, 1999 (conjecture; low-dimensional fiducials); J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves, Symmetric informationally complete quantum measurements, J. Math. Phys. 45 (2004), 2171–2180 (SIC-POVMs in low dimensions, including d = 3). The vector (0, 1, −1)/√2 is a member of the known one-parameter family of d = 3 fiducials. Parent problem: WeylHeisenbergSIC.fiducial_exists (Zauner's conjecture).

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LefebvreVariations

/-- Zauner's conjecture in dimension 3: the vector `ψ = (0, 1, -1)/√2` is a
Weyl-Heisenberg fiducial (all eight nonidentity displacements have squared overlap
`1/4 = 1/(d+1)`). Source: Zauner, thesis (Vienna 1999), Chapter 3; Renes, Blume-Kohout,
Scott, Caves, "Symmetric informationally complete quantum measurements",
J. Math. Phys. 45 (2004), Sec. 5 (d = 3 solution). Same form as the platform's
`WeylHeisenbergSIC.fiducial_exists` with `d = 3`. -/
theorem fiducial_d3 :
    ∃ ψ : ZMod 3 → ℂ,
      (∑ x : ZMod 3, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 3, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 3, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (((3 : ℕ) : ℝ) + 1)⁻¹ := by
  sorry

end LefebvreVariations
