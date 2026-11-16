-- Prove2me | Theorems.Thm_MixedCloning_Optimal_Supplement_proposition_26
-- name    : MixedCloning.Optimal.Supplement.proposition_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:17:02.229202+00:00
-- url     : https://prove2.me/theorems/0c954c57-e002-481d-b5c7-874dc3233b6d
-- title:
--   Proposition 26 — lower bound for transposing projector states
-- statement:
--   Let $d\ge2$, $r\ge1$ with $2r\le d$, $k\ge1$, $n\ge0$ be integers and $0<\varepsilon\le1/16$. A **rank-$r$ projector state** is $P/r$, where $P$ is an orthogonal projector of rank $r$ on $\mathbb C^d$. Let $T$ be a channel from $(\mathbb C^d)^{\otimes n}$ to $(\mathbb C^d)^{\otimes k}$ such that for every such $P$,
--   $$F\Bigl(T\bigl((P/r)^{\otimes n}\bigr),\bigl((P/r)^{\mathsf T}\bigr)^{\otimes k}\Bigr)\ge1-\varepsilon .$$
--   Then
--   $$n\ge\frac{krd}{8\varepsilon}.$$
--
--   The paper writes $n=\Omega(krd/\varepsilon)$; its proof (p. 29, Step 5, via Lemma 17) yields the constant $1/8$. This is the lower-bound half of Theorem 27 at rank $r\le d/2$.
--
--   **Formalization Note** $F$ is the squared fidelity; the transpose is the computational-basis transpose. The input count $n=0$ is allowed (the empty tensor power is one-dimensional).
--
--   Differences from the source:
--   - encoding: $n=\Omega(krd/\varepsilon)$ → $n\ge krd/(8\varepsilon)$; reason: the proof on p. 29 supplies the explicit constant 1/8
--   - encoding: $\varepsilon\le1/16$ → $0<\varepsilon\le1/16$; reason: the bound krd/ε is undefined at ε = 0, and for ε < 0 the fidelity hypothesis 1 − ε > 1 cannot be met
--   - encoding: rank-$r$ projector states, $r\le d/2$, $k$ output copies → $1\le r$, $2r\le d$, $1\le k$; reason: $P/r$ is a state only for $r\ge1$, $2r\le d$ is the integer form of $r\le d/2$, and $k\ge1$ is the paper's standing count of output copies (at $r=0$ or $k=0$ the conclusion is $0\le n$)
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 27, Proposition 26; proof pp. 27–29, Step 5 on p. 29

import Definitions.Def_MixedCloning_Optimal_Supplement_Transposition

noncomputable section
open Matrix MixedCloning.Optimal
open scoped Matrix ComplexConjugate

namespace MixedCloning.Optimal.Supplement
attribute [local instance] Classical.propDecidable Classical.decEq

theorem proposition_26 (d r n k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : 2*r ≤ d)
    (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) (heps16 : eps ≤ 1/16)
    (T : Transposer d n k) (hT : QAlgorithms.IsChannel T)
    (htrans : ∀ P : Op (Fin d), IsProjector r P →
      1-eps ≤ fidelity (T (tensorPower n (projectorState r P)))
        (tensorPower k (projectorState r P)ᵀ)) :
    (k : ℝ)*r*d/(8*eps) ≤ n := by sorry

end MixedCloning.Optimal.Supplement
