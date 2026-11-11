-- Prove2me | Theorems.Thm_HypercliqueRefutation_FourClique_observation_2_5
-- name    : HypercliqueRefutation.FourClique.observation_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:26.851187+00:00
-- url     : https://prove2.me/theorems/fc4a01d9-b49e-41c9-9464-badbd9caedad
-- title:
--   Observation 2.5 — alternating-walk equality (corrected: ℓ is fixed)
-- statement:
--   Let K be a characteristic-zero field. Let n,n_A,n_B,L be nonnegative integers, let A_a and B_b be symmetric n×n matrices over K, and let h,w satisfy the full symmetrized cancellation identity of Eq.(2). For each fixed ℓ put P^{(ℓ)}[x,y]=∑_{z,a,b}h^{(ℓ)}_{a,b}A_a[x,z]B_b[z,y]. Then
--
--   $$D(A,B)=\sum_{x,y\in[n],\,\ell\in[L]}w_\ell P^{(\ell)}[x,y]P^{(\ell)}[y,x].$$
--
--   Both symmetry assumptions and both terms of Eq.(2) are retained. The statement holds without any nonnegativity assumption or exclusion of coinciding walk indices. It expresses exactly the weighted recovery equality; it makes no construction-time claim.
--
--   Differences from the source:
--   - correction: the definition of P^(ℓ) also sums over ℓ → ℓ is fixed and only z,a,b are summed; reason: with m=8,k=0,n=1,n_A=L=16,n_B=1, h_(a,0)^(ℓ)=1[a=ℓ], w=1, A_0=B_0=[1] and other A=0, the literal printed formula gives Q=16 while D=1; fixing ℓ gives Q=D=1
--   - generalization: h,w are the family of Lemma 2.4 with its sizes, signs, rational weights and sparsity → any n_A,n_B,L and any scalar h,w satisfying Eq.(2); reason: the equality uses only Eq.(2) and matrix symmetry; the entire source family is included and no source clause of this equality is lost
--   - reading: the arrays have an implicit scalar domain → an arbitrary characteristic-zero field K, including rational, real and complex scalars; reason: this makes the scalar domain explicit while retaining both symmetry assumptions and all scalar instances selected in the brief
--   - encoding: indices range over [n],[n_A],[n_B],[L] → Fin n, Fin n_A, Fin n_B and Fin L with finite sums; reason: these are the same zero-based finite ranges, including empty ones
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026), held source.pdf SHA-256 fda90f18867fd07883366a1bc49a8afa652b8712f71402e11ccd45e6633b127a; Observation 2.5, p.5, using Lemma 2.4 Eq.(2), p.4.

import Mathlib
import Definitions.Def_HypercliqueRefutation_FourClique_WeightedProducts

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique

/-- Observation 2.5, p.5, corrected: l is fixed in the definition of P^(l).
    Both input families are symmetric. The equality uses Eq.(2), not sparsity.
    Generalized to every characteristic-zero field, all dimensions and every
    cancellation family satisfying Eq.(2); the source family is a special case. -/
theorem observation_2_5 {K : Type*} [Field K] [CharZero K]
    {n nA nB L : ℕ}
    (h : Fin L → Fin nA → Fin nB → K) (w : Fin L → K)
    (hw : CancellationIdentity h w)
    (A : Fin nA → Matrix (Fin n) (Fin n) K)
    (B : Fin nB → Matrix (Fin n) (Fin n) K)
    (hA : ∀ a, (A a).IsSymm) (hB : ∀ b, (B b).IsSymm) :
    alternatingContraction A B = weightedTrace h w A B := by sorry

end HypercliqueRefutation.FourClique
