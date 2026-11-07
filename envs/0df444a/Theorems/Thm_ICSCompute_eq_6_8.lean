-- Prove2me | Theorems.Thm_ICSCompute_eq_6_8
-- name    : ICSCompute.eq_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:22.427851+00:00
-- url     : https://prove2.me/theorems/e4e3ab9c-741d-439c-b47a-f9fd54d61b4e
-- title:
--   Eq. (6.8) — the blocks of a unitary $B$ on $R_i,E_i$
-- statement:
--   Let $B$ be a unitary operator on a qubit $R_i$ together with an auxiliary register $E_i$, and write $B^{u,v} := (\langle u|\otimes I)B(|v\rangle\otimes I)$ for $u,v\in\{0,1\}$. Then for all $u,u'\in\{0,1\}$,
--   $$\sum_{v\in\{0,1\}} B^{u,v}\big(B^{u',v}\big)^\dagger = \mathbb 1[u = u']\, I_{\mathcal L(H_{E_i})}. \tag{6.8}$$
--   This is the $(u,u')$ block of $BB^\dagger = I$; it is applied to $B = B_{i,a} = V_i(U_{i,a}\otimes I_{E_i})$.
--
--   Differences from the source:
--   - generalization: B = B_{i,a} = V_i (U_{i,a} ⊗ I) with unitary V_i, U_{i,a} on a qubit auxiliary register → any unitary B on Bool × E with E any finite index type; reason: the paper derives (6.8) from unitarity of B_{i,a} only; B_{i,a} is a special case
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), proof of Theorem 6.1, eq. (6.8), p.34 (PDF p.36)

import Mathlib
import Definitions.Def_ICSCompute_Tmat

namespace ICSCompute

/-- **Eq. (6.8)** (Shmueli, *What Can Be Computed with Indefinite Causal Structure?*,
arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, proof of Theorem 6.1, eq. (6.8),
p.34 (PDF p.36)).

"Recall that for all `i, a` the matrix `B_{i,a}` is unitary and thus `B_{i,a} B_{i,a}† = I`. For
`u, u′ ∈ {0,1}`, taking the `(u, u′)` part of the equality `B_{i,a} B_{i,a}† = I` gives
`∑_{v ∈ {0,1}} B^{u,v}_{i,a} (B^{u′,v}_{i,a})† = 1[u = u′] I_{L(H_{Eᵢ})}`."

**Formalization Note** Stated for every unitary `B` on `Bool × E` with `E` any finite index type;
the paper's `B_{i,a} = Vᵢ (U_{i,a} ⊗ I)` with unitary `Vᵢ`, `U_{i,a}` is a special case. -/
theorem eq_6_8 {E : Type*} [Fintype E] [DecidableEq E] (B : Matrix (Bool × E) (Bool × E) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Bool × E) ℂ) (u u' : Bool) :
    ∑ v : Bool, Bsub B u v * (Bsub B u' v).conjTranspose = if u = u' then 1 else 0 := by sorry

end ICSCompute
