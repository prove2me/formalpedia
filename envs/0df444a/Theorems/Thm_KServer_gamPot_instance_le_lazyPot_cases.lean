-- Prove2me | Theorems.Thm_KServer_gamPot_instance_le_lazyPot_cases
-- name    : KServer.gamPot_instance_le_lazyPot_cases
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T18:41:56.36847+00:00
-- url     : https://prove2.me/theorems/2c8319b3-48dd-4b74-a552-66c1383fa703
-- title:
--   The configuration lemmas for the auxiliary potential Gamma
-- statement:
--   In an **arbitrary** metric space, an instance of the auxiliary potential $\Gamma_{w,r}$ is bounded by the lazy potential $\Psi_{w,r}$ in each of the following configurations of its witnesses, and one further inequality lets a witness be moved:
--
--   1. $f = d$;
--   2. $p$ and $r$ both lie on a geodesic between $b$ and $b'$;
--   3. (*a reduction, not a bound*) when $b = b'$ and $p$ lies on a geodesic between $X$ and $b$, the instance at $p$ is at most the instance at $X$;
--   4. $b = b'$ and $f = p$;
--   5. $b = b'$, $f = b$, and $q$ lies on a geodesic between $p$ and $b$;
--   6. $b = b'$, $d = p$ and $d' = b$;
--   7. $d' = b$ and $q$ lies on a geodesic between $b'$ and $f$;
--   8. $f = b'$ and $d' = b$.
--
--   ## Role
--
--   These are the configurations into which the proof that $\Gamma_{w,r} \le \Psi_{w,r}$ in the city-block plane decomposes, once every free point has been pushed out to a corner of a bounding rectangle. As with the corresponding statements for $\Lambda$, the plane itself has already done its work by then: what the rectangle supplies is exactly the betweenness relations appearing above, and the arguments are the usual mixture of the triangle inequality, the Lipschitz property and quasiconvexity, valid in any metric space.
--
--   The third item is of a different character from the rest. In the case $b = b'$ the free point $p$ can be moved out to the corner $X$ opposite $b$ before the analysis begins — the Lipschitz property pays for the two occurrences of $pb$ against $Xb$, and the triangle inequality pays for the change in $rp$. Only after that move do the remaining cases apply, which is why they may assume $f$, $d$ and $d'$ related to $p$ as they do.
--
--   Item 4 is the one place where a single instance of $\Psi_{w,r}$ does not suffice: the bound is the *average* of two, one taken at $b$ and one at $q$, and it is valid because the inequality is linear. Items 1, 5 and 8 need the quasiconvexity inequality, which delivers a minimum of two rematchings; in item 1 the two branches are exchanged by interchanging $b$ with $b'$, under which the expression is invariant, while in items 5 and 8 they close independently on different instances of $\Psi_{w,r}$.
--
--   **Formalization note.** Each configuration reduces to a single linear-arithmetic combination of one or two instances of $\Psi_{w,r}$, a few triangle inequalities, at most one application of the Lipschitz property in pinned two-point form, and at most two applications of pairwise quasiconvexity. Where a quasiconvexity branch is disposed of by a symmetry, the case is factored through an auxiliary statement taking the branch as a hypothesis, applied twice with permuted arguments.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 6, Cases 1, 2, the reduction opening Case 3, and Cases 3.1, 3.2, 3.3.1, 4.1 and 4.2.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem gamPot_instance_le_lazyPot_cases (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M) :
    (∀ p q b b' d' f : M,
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist f d' - workFnU C₀ σ ![r, q, f] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b b' d d' f : M, dist p b + dist p b' = dist b b' →
        dist r b + dist r b' = dist b b' →
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ lazyPot C₀ σ r)
    ∧ (∀ p X q b d d' f : M, dist X p + dist p b = dist X b →
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, p, f]
        ≤ (-dist r X + (dist X b + dist X b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, X, f])
    ∧ (∀ p q b d d' : M,
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q p - workFnU C₀ σ ![r, p, p] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b d d' : M, dist q p + dist q b = dist p b →
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q b - workFnU C₀ σ ![r, p, b] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b f : M,
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist p b - workFnU C₀ σ ![r, q, p] - workFnU C₀ σ ![r, q, b]
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b b' d f : M, dist q b' + dist q f = dist b' f →
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist d b - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, b]
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b b' d : M,
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist d b - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, b]
        + dist q b' - workFnU C₀ σ ![r, p, b'] ≤ lazyPot C₀ σ r) := by sorry

end KServer
