-- Prove2me | Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
-- name    : M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/65c391bf-b629-5e5f-991c-bf315143cd0d
-- title:
--   Local norm scales the valuation by the residue degree
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a height one prime of the ring of integers $\mathcal{O}_K$, and let $w$ be an element of $v$'s set of extensions to $\mathcal{O}_L$, that is, a height one prime of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$. Write $K_v$ and $L_w$ for the $v$-adic and $w$-adic completions, each carrying its canonical valuation, and regard $L_w$ as an algebra over $K_v$. Then for every $y \in L_w$ the valuation of the algebra norm $N_{L_w/K_v}(y) \in K_v$ equals the valuation of $y$ raised to the power $\mathrm{inertiaDeg}'$ of $v$ below $w$, i.e. the degree of the residue field extension of $w$ over $v$ in Mathlib's unconditional form `Ideal.inertiaDeg'`. The valuations take values in the multiplicatively written group with zero $\mathbb{Z}_{m0}$, so the asserted identity is the multiplicative form of $\mathrm{ord}_v(N_{L_w/K_v}(y)) = f(w\mid v)\,\mathrm{ord}_w(y)$; no normality of $L/K$ is assumed, and the case $y = 0$ is included.
--
--   This is the standard computation of the valuation of a local norm in terms of the residue degree of $w$ over $v$. It is used wherever local norms between completions have to be measured, for instance in the comparison of valuations under base change of a prime and in the computation of local integrals over ideles in the automorphic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (y : w.1.adicCompletion L) :
    Valued.v (Algebra.norm (v.adicCompletion K) y) =
      Valued.v y ^ Ideal.inertiaDeg' v.asIdeal w.1.asIdeal := by sorry
