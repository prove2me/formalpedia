-- Prove2me | Theorems.Thm_MixedCloning_Optimal_proposition_11
-- name    : MixedCloning.Optimal.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:06:01.735505+00:00
-- url     : https://prove2.me/theorems/9e004a16-137c-429e-9595-819474231d8a
-- title:
--   Proposition 11 — lower bound for projector-state cloning
-- statement:
--   Let $d\ge2$, $r\ge1$, $2r\le d$, $k\ge1$, $n\ge0$, and $0<\varepsilon\le1/16$. Let $C$ be a channel such that for every rank-$r$ orthogonal projector $P$, writing $\rho=P/r$,
--
--   $$F(C(\rho^{\otimes n}),\rho^{\otimes(n+k)})\ge1-\varepsilon.$$
--
--   Then
--
--   $$n\ge\frac{krd}{8\varepsilon}.$$
--
--   The paper writes $\Omega(krd/\varepsilon)$; the proof through Lemma 17 yields constant $1/8$. Projector states alone already require this many samples, even though their spectrum is known.
--
--   Differences from the source:
--   - encoding: Ω(krd/ε) → n ≥ krd/(8ε); reason: Lemma 17 supplies the explicit constant 1/8
--   - encoding: m and r ≤ d/2 → m = n+k and 2r ≤ d with 0 < ε; reason: these are the section conventions and the domain of the printed divisions
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 16, Proposition 11; proof completed by Lemma 17 on p. 20

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem proposition_11 (d r n k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : 2*r ≤ d)
    (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) (heps16 : eps ≤ 1/16)
    (C : Cloner d n (n+k)) (hC : QAlgorithms.IsChannel C)
    (hclone : ∀ P : Op (Fin d), IsProjector r P →
      1-eps ≤ fidelity (C (tensorPower n (projectorState r P)))
        (tensorPower (n+k) (projectorState r P))) :
    (k : ℝ)*r*d/(8*eps) ≤ n := by sorry

end MixedCloning.Optimal
