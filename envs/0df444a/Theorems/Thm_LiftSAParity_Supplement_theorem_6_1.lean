-- Prove2me | Theorems.Thm_LiftSAParity_Supplement_theorem_6_1
-- name    : LiftSAParity.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:17:45.126148+00:00
-- url     : https://prove2.me/theorems/ca838945-57b2-489e-881a-392086a21cf0
-- title:
--   Theorem 6.1 — a sufficient condition for the canonical distribution $\mathcal D^\varphi$ to be fooling
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $\varphi$ be a CNF formula over $n$ blocks of $\ell$ variables, let $d\in\mathbb N$, and let $m$ be the maximum number of clauses of $\varphi$ whose variables all lie in some set of at most $d$ blocks. Suppose that the canonical family $\mathcal D^\varphi$ is a block $d$-local distribution for $\varphi$. Suppose also that every blockwise partial assignment that falsifies no clause, when extended uniformly to any set of at most $d$ blocks, falsifies a clause with probability at most $p$, where $p<1$. Put
--   $$
--   \varepsilon=\frac{C\,m^{2.2}\,2^{-\sqrt t/10}}{1-p}.
--   $$
--   Then for all $r,t\in\mathbb N$ with $rt\le d$:
--
--   1. $\mathcal D^\varphi$ satisfies the first $(r,t,\varepsilon)$-fooling condition;
--   2. if moreover $t\le r/10$, then $\mathcal D^\varphi$ is $(r,t,\varepsilon+2^{-r/2})$-fooling.
--
--   This is the paper's route from Bazzi's theorem (polylogarithmic independence fools CNFs) to fooling distributions; with Theorem 5.4 it gives the binary pigeonhole lower bound, Theorem 1.4.
--
--   **Formalization Note** $\mathcal D^\varphi$ is `canonDist φ`, $m$ is `maxLocalClauses φ d`, and the hypothesis on $p$ is `UniformExtFalsifyBound φ d p`. $m^{2.2}$ and $2^{-\sqrt t/10}$ are real powers, and $t\le r/10$ is written $10t\le r$. The constant $C$ is chosen once, before all other parameters.
--
--   Differences from the source:
--   - reading: "does not falsify any clause" and "falsifies a clause" for partial assignments → no clause whose variables all lie in the assigned blocks is falsified / some clause whose variables all lie in I × [ℓ] is falsified; reason: a partial assignment can falsify only a clause all of whose variables it assigns
--   - encoding: t ≤ r/10 → 10 * t ≤ r in ℕ; reason: equivalent for natural numbers
--   - encoding: Cl^t(A), the unique inclusion-minimal set → the intersection of all sets of blocks outside which A is t-safe; reason: equal for every nonempty affine A by the proof of Lemma 5.1
--   - generalization: integers n, ℓ ≥ 1 (§2, p.7) and "For d ≥ 1" (p.20) → n, ℓ, d : ℕ, including 0; reason: the statement keeps its meaning there; for d = 0, rt ≤ 0 and 10t ≤ r force t = 0 or I = ∅, where sampling is uniform and the bounds hold since ε ≥ 0; the Lean statement specializes to the printed one
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §6.1, Theorem 6.1, p.20

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_Supplement_IsFooling
import Definitions.Def_LiftSAParity_Supplement_canonDist

namespace LiftSAParity

namespace Supplement

/-- **Theorem 6.1** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary
Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §6.1, p.20): "Let φ be a CNF
formula with m = the maximum number of clauses of φ whose variables all lie in some set of at most
d blocks. Let D^φ be a d-local distribution for φ. Suppose every blockwise partial assignment that
does not falsify any clause, when extended uniformly to any set of at most d blocks, falsifies a
clause with probability at most p < 1. For every r, t ∈ ℕ with rt ≤ d, D^φ satisfies the first
(r, t, ε)-fooling condition with ε = C m^{2.2} 2^{−√t/10} / (1 − p), where C > 0 is an absolute
constant. If also t ≤ r/10, then D^φ is (r, t, ε + 2^{−r/2})-fooling."

**Formalization Note** One absolute `C > 0`, chosen before every other parameter. `D^φ` is the
canonical family `canonDist φ`; "D^φ is a d-local distribution for φ" is
`IsBlockLocalDist φ d (canonDist φ)`. `m = maxLocalClauses φ d`; `m^{2.2}` and `2^{−√t/10}` are
real powers. `t ≤ r/10` is `10 t ≤ r` in `ℕ`. -/
theorem theorem_6_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (n ℓ d : ℕ) (φ : CNF (Fin n × Fin ℓ)) (p : ℝ),
      IsBlockLocalDist φ d (canonDist φ) → p < 1 → UniformExtFalsifyBound φ d p →
      ∀ r t : ℕ, r * t ≤ d →
        FoolCond1 d r t
          (C * (maxLocalClauses φ d : ℝ) ^ (2.2 : ℝ) * (2 : ℝ) ^ (-Real.sqrt t / 10) / (1 - p))
          (canonDist φ) ∧
        (10 * t ≤ r → IsFooling φ d r t
          (C * (maxLocalClauses φ d : ℝ) ^ (2.2 : ℝ) * (2 : ℝ) ^ (-Real.sqrt t / 10) / (1 - p) +
            (2 : ℝ) ^ (-(r : ℝ) / 2))
          (canonDist φ)) := by sorry

end Supplement

end LiftSAParity
