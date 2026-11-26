-- Prove2me | Theorems.Thm_LefebvreVariations_elliptic_prime_torsion_card_le
-- name    : LefebvreVariations.elliptic_prime_torsion_card_le
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:10:32.353917+00:00
-- url     : https://prove2.me/theorems/90b67ad9-c731-43de-a571-cf7b2140b724
-- title:
--   Lefebvre's variations, No. 144 — on a theme by Hasse and Weil: at most $\ell^2$ points of prime-order torsion on an elliptic curve over a finite field
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is the geometric core of the structure theorem for the group of rational points of an elliptic curve over a finite field.
--
--   Let $K$ be a finite field, $E/K$ an elliptic curve given by a Weierstrass equation with nonzero discriminant, and $E(K)$ its (finite) group of $K$-rational points, including the point at infinity $O$. For every prime number $\ell$,
--
--   $$
--   \#\{\, P \in E(K) : \ell P = O \,\} \;\le\; \ell^{2}.
--   $$
--
--   The prime $\ell$ may equal the characteristic of $K$ (in which case the bound is even $\le \ell$, because $E[p](\overline K)$ is trivial or cyclic of order $p$) or may differ from it (then $E[\ell](\overline K) \cong (\mathbb{Z}/\ell)^2$ and $E(K)[\ell]$ is a subgroup of it). The statement is the missing algebro-geometric step in proving that $E(K) \cong \mathbb{Z}/n_1 \times \mathbb{Z}/n_2$ with $n_1 \mid n_2$: once every $\ell$-torsion subgroup of the finite abelian group $E(K)$ has at most $\ell^2$ elements, a purely group-theoretic argument (rank at most two) gives that structure.
--
--   **Formalization Note** The curve is a `WeierstrassCurve K` with the typeclass `E.IsElliptic` (unit discriminant), and points are `E.toAffine.Point` (the point at infinity `zero`, plus affine nonsingular points `some x y h`), whose `AddCommGroup` structure is Mathlib's chord-and-tangent law. $\ell P = O$ is `ℓ • P = 0` with the natural-number scalar action, and the cardinality is `Nat.card` of the subtype. `Fintype K` and `DecidableEq K` mirror the hypotheses of the platform statement `ECDLP.point_group_structure`. No separability or perfectness assumptions are needed: finite fields are perfect.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `ECDLP.point_group_structure` (the group of points of an elliptic curve over a finite field is a product of at most two cyclic groups). The reduction proves, entirely in Lean, that a finite abelian group whose $\ell$-torsion has at most $\ell^2$ elements for every prime $\ell$ is a product of at most two cyclic groups; what remains is exactly this torsion bound. It is the geometric content of the base statement with the group algebra removed, so it is equivalent to it given that proved lemma, not a strictly weaker claim. It is a classical theorem (Silverman, III.6.4 and V.3.1).
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Corollary III.6.4(b) (E[m] over an algebraically closed field of characteristic prime to m is (Z/m)^2) and Theorem V.3.1 (E[p^e] is trivial or Z/p^e in characteristic p); L. C. Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., Theorem 3.2 and Theorem 4.1 (E(F_q) is a product of at most two cyclic groups, deduced from exactly this torsion bound). Origin of this statement: it is the missing step of a reduction of the open platform theorem ECDLP.point_group_structure (the structure E(K) = Z/n1 x Z/n2 with n1 | n2) to it; the remaining implication is pure finite-abelian-group theory and is fully proved in Lean in the accompanying reduction file.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem elliptic_prime_torsion_card_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card {P : E.toAffine.Point // ℓ • P = 0} ≤ ℓ ^ 2 := by sorry
end LefebvreVariations
