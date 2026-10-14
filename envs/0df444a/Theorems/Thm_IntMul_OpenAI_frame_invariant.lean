-- Prove2me | Theorems.Thm_IntMul_OpenAI_frame_invariant
-- name    : IntMul.OpenAI.frame_invariant
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T13:55:27.396382+00:00
-- url     : https://prove2.me/theorems/d261dcaf-9c9a-400a-bac9-dc32e84b8bf0
-- title:
--   Frames commute with pointwise linear networks
-- statement:
--   Let $R$ be a commutative ring, $\mathcal W$ a finite set of wire roles and $\Omega$ an address set. Each wire carries an array in $R^\Omega$. A gate $g=(C_g,S_g,D_g)$ consists of the following:
--   - a coefficient matrix $C_g\in R^{\mathcal W\times\mathcal W}$, applied pointwise at every address, $(C_g f)_w(\omega)=\sum_{w'}C_g(w,w')f_{w'}(\omega)$;
--   - the set $S_g$ of wires it touches, with $C_g$ the identity on rows outside $S_g$ and rows in $S_g$ reading only wires in $S_g$;
--   - an invertible $R$-linear *frame* $D_g$ of $R^\Omega$.
--
--   Fix source frames $D^{\rm in}_w$ and sink frames $D^{\rm out}_w$. The *physical* execution keeps, for each wire, its current frame $F_w$, starting from $F_w=D^{\rm in}_w$ on the supplied arrays $f$. Before gate $g$ it applies the edge operator $D_gF_w^{-1}$ to each touched wire, then applies $C_g$ pointwise, and sets $F_w=D_g$ on touched wires. After the last gate it applies the sink edge $D^{\rm out}_wF_w^{-1}$. The *logical* execution applies the gates $C_g$ pointwise to $g=(D^{\rm in})^{-1}f$. Then for every wire $w$,
--   $$\text{physical output}_w \;=\; D^{\rm out}_w\big(\text{logical output}_w\big),$$
--   so the implemented operator is $D^{\rm out}\,S_\Omega\,(D^{\rm in})^{-1}$.
--
--   This is the representation principle of §3.2 (equation (5)) of the OpenAI preprint *Integer multiplication below $n\log n$*. It allows a finite linear network to be run on whole arrays while each wire's array changes representation along the way. Every κ-saving construction (the OpenAI networks, Colkitt's and Jain's rounds) uses it to turn cheap edge operators into a full address interchange or butterfly layer.
--
--   **Formalization Note** A gate is a triple `(C, S, D)` in a list, applied in order. The physical state is the pair (current frames, stored arrays).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026 , Section 3.2, equation (5) and Figure 2

import Mathlib
open Finset

namespace IntMul.OpenAI

theorem frame_invariant {Wr Ω R : Type*} [CommRing R] [Fintype Wr] [DecidableEq Wr]
    (gates : List (Matrix Wr Wr R × Finset Wr × ((Ω → R) ≃ₗ[R] (Ω → R))))
    (hgates : ∀ g ∈ gates, ∀ w w', (w ∉ g.2.1 → g.1 w w' = if w = w' then 1 else 0) ∧
      (w ∈ g.2.1 → w' ∉ g.2.1 → g.1 w w' = 0))
    (Din Dout : Wr → ((Ω → R) ≃ₗ[R] (Ω → R))) (f : Wr → Ω → R) :
    let physical := gates.foldl
      (fun (st : (Wr → ((Ω → R) ≃ₗ[R] (Ω → R))) × (Wr → Ω → R)) g =>
        (fun w => if w ∈ g.2.1 then g.2.2 else st.1 w,
         fun w ω => ∑ w', g.1 w w' *
           (if w' ∈ g.2.1 then g.2.2 ((st.1 w').symm (st.2 w')) else st.2 w') ω))
      (Din, f)
    let logical := gates.foldl (fun (h : Wr → Ω → R) g => fun w ω => ∑ w', g.1 w w' * h w' ω)
      (fun w => (Din w).symm (f w))
    ∀ w, Dout w ((physical.1 w).symm (physical.2 w)) = Dout w (logical w) := by sorry

end IntMul.OpenAI
