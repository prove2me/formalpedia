-- Prove2me | Theorems.Thm_GroverWiki_phaseOracle_reflection_perp
-- name    : GroverWiki.phaseOracle_reflection_perp
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T14:36:25.441982+00:00
-- url     : https://prove2.me/theorems/a3ccf7b7-e841-4be4-9f1e-0d3a94f47903
-- title:
--   $U_\omega$ acts on the plane $\mathrm{span}\{|s'\rangle, |\omega\rangle\}$ as the reflection across $|s'\rangle$
-- statement:
--   Let $f\colon\{0,\dots,N-1\}\to\{0,1\}$ have exactly one index $\omega$ with $f(\omega) = 1$, let $U_\omega|x\rangle = (-1)^{f(x)}|x\rangle$, and let $|s'\rangle = \frac{1}{\sqrt{N-1}}\sum_{x\ne\omega}|x\rangle$. Then for all $a, b \in \mathbb C$,
--
--   $$U_\omega\bigl(a|\omega\rangle + b|s'\rangle\bigr) = -a|\omega\rangle + b|s'\rangle .$$
--
--   That is, on the plane spanned by $|s'\rangle$ and $|\omega\rangle$ the oracle is the reflection across $|s'\rangle$ (the reflection at the hyperplane orthogonal to $|\omega\rangle$); in particular it maps the plane to itself.
--
--   **Formalization Note** For $N = 1$ the sum defining $|s'\rangle$ is empty and $|s'\rangle = 0$; the statement then only concerns multiples of $|\omega\rangle$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Geometric proof" (PDF p. 4)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- In the plane spanned by `|s'⟩` and `|ω⟩`, `U_ω` acts as the reflection across `|s'⟩`. -/
theorem phaseOracle_reflection_perp {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (a b : ℂ) :
    phaseOracle f *ᵥ (a • ket ω + b • perpState ω) = (-a) • ket ω + b • perpState ω := by sorry

end GroverWiki
