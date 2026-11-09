-- Prove2me | Theorems.Thm_GenericGroupWE_Main_eq_29_30
-- name    : GenericGroupWE.Main.eq_29_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:53.399726+00:00
-- url     : https://prove2.me/theorems/0845a78c-2256-431f-81c9-70017027f775
-- title:
--   §6.4, eqs. (29)–(30) — Surviving column relations span at most ρ² dimensions
-- statement:
--   For a nonzero represented stack $A=\sum_b\lambda_bA(b)$ of rank $\rho$, fix $d\ge1$ and stack the columns $c_i=(C_{iU})_{|U|\le d-1}$, where $0U=U$ and $iU=U\cup\{i\}$. Their span has dimension $\delta$ satisfying
--
--   $$1\le\delta\le\rho^2.$$
--
--   For every relation $\sum_i\kappa_ic_i=0$, set $K(b)=\kappa_0+\sum_{i=1}^N\kappa_ib_i$. Then for every listed weight $h$ and polynomial $f$ of degree at most $2d-1$,
--
--   $$\sum_b\lambda_bK(b)h(b)f(b)=0.$$
--
--   Both the dimension bound and the surviving relation are retained in this item.
--
--   Differences from the source:
--   - generalization: the unsatisfiable low-rank prime-field regime of §6.4 → any field and any nonzero represented stack; reason: the two displayed claims use only the assignment-table identities, so they specialize to every stack in the source regime
--   - encoding: finite indexed families and field residues → Fin-indexed families and ZMod prime fields; reason: zero-based indices and explicit finite carriers change no mathematical instance
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §6.4, eqs. (29)–(30), PDF p. 27 (printed p. 26).

import Definitions.Def_GenericGroupWE_Main_Tables

namespace GenericGroupWE.Main
open scoped BigOperators

theorem eq_29_30 (K : Type*) [Field K] (N d : ℕ) (hd : 1 ≤ d)
    (coefficients : BooleanAssignment N → K)
    (hne : representedStack (d := d) coefficients ≠ 0) :
    let A := representedStack (d := d) coefficients
    1 ≤ survivingDimension hd A ∧ survivingDimension hd A ≤ A.rank ^ 2 ∧
    ∀ κ : Option (Fin N) → K,
      (∑ i, κ i • survivingColumn hd A i) = 0 →
      ∀ (h : WeightLabel N d) (f : MvPolynomial (Fin N) K), f.totalDegree + 1 ≤ 2*d →
        ∑ b, coefficients b * affineBit κ b * stackWeight h b *
          MvPolynomial.eval (booleanPoint b) f = 0 := by sorry

end GenericGroupWE.Main
