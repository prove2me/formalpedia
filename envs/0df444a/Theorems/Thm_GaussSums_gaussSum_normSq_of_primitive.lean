-- Prove2me | Theorems.Thm_GaussSums_gaussSum_normSq_of_primitive
-- name    : GaussSums.gaussSum_normSq_of_primitive
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T11:49:12.144758+00:00
-- url     : https://prove2.me/theorems/c55c7d3e-6cec-4e66-8e10-eda3bc863e14
-- title:
--   The modulus of a Gauss sum of a primitive character
-- statement:
--   **The modulus of a Gauss sum attached to a primitive character.**
--
--   For a Dirichlet character $\chi$ modulo $q$ and an additive character $\psi$ of
--   $\mathbb{Z}/q\mathbb{Z}$, the Gauss sum is
--
--   $$g(\chi,\psi) \;=\; \sum_{a \bmod q} \chi(a)\,\psi(a).$$
--
--   If **both** characters are primitive, then the sum has modulus exactly $\sqrt q$:
--
--   $$\bigl|g(\chi,\psi)\bigr|^2 \;=\; q.$$
--
--   A Gauss sum has $q$ terms each of modulus at most $1$, so the trivial bound is $q$; the
--   theorem says there is complete square-root cancellation. This is the archetypal example of
--   such cancellation in analytic number theory, and it is what makes Gauss sums the standard
--   bridge between multiplicative and additive characters: it converts the functional equation of
--   a Dirichlet $L$-function into one with a root number of modulus $1$, and it supplies the
--   normalising factor in the Pólya–Vinogradov inequality and in the Fourier expansion of
--   $\chi$ in additive characters.
--
--   Primitivity is essential in both arguments. If $\chi$ is induced from a character of smaller
--   conductor, or if $\psi$ is non-primitive, the sum degenerates and can even vanish, so no such
--   identity can hold.
--
--   The modulus $q$ here is **arbitrary**, composite included; the familiar special case is the
--   quadratic Gauss sum modulo a prime $p$, of modulus $\sqrt p$.
--
--   **Formalization note.** `gaussSum` and `AddChar.IsPrimitive` are Mathlib's; the statement is
--   given as $\|g\|^2 = q$ over $\mathbb{R}$ rather than $\|g\| = \sqrt q$, which avoids a square
--   root and is equivalent since norms are non-negative.
-- source:
--   Classical; see Iwaniec & Kowalski, *Analytic Number Theory*, §3.4, and Montgomery & Vaughan, *Multiplicative Number Theory I*, §9.1. Lean proof extracted from `Salt/LS/GaussSum.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace GaussSums

theorem gaussSum_normSq_of_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {ψ : AddChar (ZMod q) ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (q : ℝ) := by sorry

end GaussSums
