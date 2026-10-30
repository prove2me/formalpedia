-- Prove2me | Theorems.Thm_HighDimProbAudit_Grothendieck_sphere_linearization
-- name    : HighDimProbAudit.Grothendieck.sphere_linearization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:37:12.948924+00:00
-- url     : https://prove2.me/theorems/f43a6cb3-5940-4c92-9456-c4e9f9963e70
-- title:
--   Lemma 3.7.7 — unit-sphere linearization with exact β
-- statement:
--   Fix $n\in\mathbb N$ and set
--   $$\beta=\frac{2}{\pi}\log(1+\sqrt2).$$
--   Write $S^{n-1}=\{u\in\mathbb R^n:\|u\|_2=1\}$. There exist a real Hilbert space $H$ and transformations $\Phi,\Psi:S^{n-1}\to S(H)$, where $S(H)=\{z\in H:\|z\|=1\}$, such that
--   $$\frac{2}{\pi}\arcsin\langle\Phi(u),\Psi(v)\rangle=\beta\langle u,v\rangle\qquad(u,v\in S^{n-1}).$$
--   Inverse sine has its principal real branch. Both transformations have exactly unit-norm outputs. The space and maps are common to all pairs of inputs, and the space can be infinite dimensional. This is the unit-sphere identity used in the full-constant version of Grothendieck’s inequality.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ with their Euclidean inner product → EuclideanSpace ℝ (Fin n); reason: Fin n relabels the finite coordinates; the norm and inner product are the Euclidean ones
--   - encoding: there exist a Hilbert space H and transformations → existential carrier H, normed additive group and real inner product structures, completeness, then maps; reason: the chosen structures specify the real Hilbert space before every input vector; no linearity, continuity, separability or finite dimension is imposed
--   - encoding: Sⁿ⁻¹ and S(H) → subtypes of vectors with norm exactly one; reason: subtype codomains enforce both unit-norm clauses without an additional hypothesis
-- source:
--   Vershynin, High-Dimensional Probability: An Introduction with Applications in Data Science, Cambridge University Press, 2018, author-corrected electronic copy dated June 9, 2020, https://doi.org/10.1017/9781108231596, Lemma 3.7.7, Eq. (3.30), footnote 7, printed p. 72 (PDF p. 80).

import Mathlib

set_option autoImplicit false

namespace HighDimProbAudit.Grothendieck

/-- Lemma 3.7.7, printed p. 72 / PDF p. 80, with the exact beta of (3.30). -/
theorem sphere_linearization (n : ℕ) :
    ∃ (H : Type) (hN : NormedAddCommGroup H),
      letI := hN
      ∃ hI : InnerProductSpace ℝ H,
        letI := hI
        CompleteSpace H ∧
          ∃ Φ Ψ : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1} → {z : H // ‖z‖ = 1},
            ∀ u v, (2 / Real.pi) * Real.arcsin (inner ℝ (Φ u).val (Ψ v).val) =
              ((2 / Real.pi) * Real.log (1 + Real.sqrt 2)) * inner ℝ u.val v.val := by sorry

end HighDimProbAudit.Grothendieck
