-- Prove2me | Theorems.Thm_LowErrExt_theorem_6_19
-- name    : LowErrExt.theorem_6_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:28.99539+00:00
-- url     : https://prove2.me/theorems/b803a95b-ab54-455a-832b-de71105936f1
-- title:
--   Theorem 6.19 — $H_2$ PFR in groups of bounded torsion
-- statement:
--   Let $m\ge2$. There are constants $\underline C,C>0$ depending only on $m$ such that the following holds. Let $G$ be a finite abelian group with torsion $m$ and $\mathbf X$ a source on $G$, and let $d$ be real with $D:=2^d$. If
--   $$H_2[\mathbf X-\mathbf X]\le H_2[\mathbf X]+d,$$
--   where $\mathbf X-\mathbf X$ is the difference of two independent copies, then there is a coset $V\subseteq G$ of size at most $2^{H_2[\mathbf X]}$ with
--   $$\Pr[\mathbf X\in V]\ge\frac{1}{\underline C\,D^{C}} .$$
--
--   This is the collision-entropy form of the polynomial Freiman–Ruzsa theorem; the paper derives it from covering PFR and a weighted Balog–Szemerédi–Gowers lemma.
--
--   Differences from the source:
--   - encoding: G has torsion m → m • x = 0 for every x ∈ G; reason: the paper's meaning of bounded torsion (footnote 20, p.40); same instances
--   - encoding: C̲, C are constants depending only on m → C̲, C are positive reals chosen after m and before G, X, d; reason: the bound 1/(C̲D^C) is a probability bound only for positive constants; the proof's constants are positive
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 6.19, p.43

import Mathlib
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_iterDiff
import Definitions.Def_LowErrExt_IsCoset

namespace LowErrExt

/-- **Theorem 6.19 (H₂ PFR).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 6.19, p.43: "Let X ∼ G, where G is a finite abelian group with torsion m ≥ 2. If
H2[X−X] ≤ H2[X] + d, then there is a coset V ⊆ G of size at most 2^{H2[X]} such that
Pr[X ∈ V] ≥ 1/(C̲D^C), where C̲, C are constants depending only on m." Here D := 2^d (p.43).

**Formalization Note.** "Torsion m" is `m • x = 0` for all `x` (not "exponent exactly `m`"). The
constants are positive reals chosen after `m` and before `G`, `X`, `d`; `d` is any real number.
`X − X` is the difference of two independent copies (`diffLaw`). -/
theorem theorem_6_19 (m : ℕ) (hm : 2 ≤ m) :
    ∃ Cu C : ℝ, 0 < Cu ∧ 0 < C ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G], (∀ x : G, m • x = 0) →
        ∀ (X : PMF G) (d : ℝ), H2 (diffLaw X) ≤ H2 X + d →
          ∃ V : Set G, IsCoset V ∧ (Nat.card V : ℝ) ≤ (2 : ℝ) ^ H2 X ∧
            1 / (Cu * ((2 : ℝ) ^ d) ^ C) ≤ probOf X V := by sorry

end LowErrExt
